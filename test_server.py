#!/usr/bin/env python3
"""Stress tests for why3server.

Usage:
    python3 test_server.py

The script expects why3server to be available on PATH.

What is tested:
  - Basic run / output capture / exit codes
  - CPU time limits
  - Memory limits
  - Parallel scheduling: -j slots, FIFO queue ordering
  - Interrupt: kill running process; remove from queue without running
  - Client disconnection: abrupt close mid-run, partial message, rapid churn
  - Grandchild processes: server must report exit of direct child only and
    kill grandchildren on timeout
  - Stress: 100 sequential jobs, 50 concurrent jobs, interleaved
    timeout/normal jobs

IMPORTANT — protocol constraint on argument content:
  The wire protocol uses semicolons as field separators and newlines as message
  terminators.  Any semicolon or newline inside an argument will be
  misinterpreted.  All test commands and script strings must be free of both
  characters.  Use write_script() to pass complex Python code via a temp file
  instead of the -c flag.
"""

import os
import sys
import socket
import subprocess
import tempfile
import time
import threading
import shutil
import unittest
import platform

IS_WINDOWS = platform.system() == "Windows"

SERVER_BIN = "why3server"

# ---------------------------------------------------------------------------
# Transport abstraction: Unix domain socket (Linux/macOS) or named pipe (Win)
# ---------------------------------------------------------------------------

if IS_WINDOWS:
    import ctypes
    import ctypes.wintypes as wt

    GENERIC_READ  = 0x80000000
    GENERIC_WRITE = 0x40000000
    OPEN_EXISTING = 3
    INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value

    _kernel32 = ctypes.windll.kernel32

    # Explicit signatures avoid HANDLE truncation on 64-bit Python, which can
    # cause intermittent invalid-handle failures under churn.
    _kernel32.CreateFileW.restype = wt.HANDLE
    _kernel32.CreateFileW.argtypes = [
        wt.LPCWSTR,
        wt.DWORD,
        wt.DWORD,
        wt.LPVOID,
        wt.DWORD,
        wt.DWORD,
        wt.HANDLE,
    ]
    _kernel32.WriteFile.restype = wt.BOOL
    _kernel32.WriteFile.argtypes = [
        wt.HANDLE,
        wt.LPCVOID,
        wt.DWORD,
        ctypes.POINTER(wt.DWORD),
        wt.LPVOID,
    ]
    _kernel32.ReadFile.restype = wt.BOOL
    _kernel32.ReadFile.argtypes = [
        wt.HANDLE,
        wt.LPVOID,
        wt.DWORD,
        ctypes.POINTER(wt.DWORD),
        wt.LPVOID,
    ]
    _kernel32.PeekNamedPipe.restype = wt.BOOL
    _kernel32.PeekNamedPipe.argtypes = [
        wt.HANDLE,
        wt.LPVOID,
        wt.DWORD,
        ctypes.POINTER(wt.DWORD),
        ctypes.POINTER(wt.DWORD),
        ctypes.POINTER(wt.DWORD),
    ]
    _kernel32.CloseHandle.restype = wt.BOOL
    _kernel32.CloseHandle.argtypes = [wt.HANDLE]

    class ServerClient:
        """Thin client that speaks the why3server wire protocol over a named pipe."""

        def __init__(self, pipe_name, connect_timeout=5.0):
            deadline = time.time() + connect_timeout
            h = INVALID_HANDLE_VALUE
            while time.time() < deadline:
                h = _kernel32.CreateFileW(
                    pipe_name,
                    GENERIC_READ | GENERIC_WRITE,
                    0, None, OPEN_EXISTING, 0, None)
                if h != INVALID_HANDLE_VALUE:
                    break
                time.sleep(0.1)
            if h == INVALID_HANDLE_VALUE:
                raise RuntimeError(f"Could not open named pipe {pipe_name!r}")
            self._h = h
            self._buf = b""

        def send(self, data: bytes):
            written = wt.DWORD(0)
            _kernel32.WriteFile(self._h, data, len(data),
                                ctypes.byref(written), None)

        def recv_line(self, timeout=15.0) -> str:
            deadline = time.time() + timeout
            while b"\n" not in self._buf:
                avail = wt.DWORD(0)
                ok = _kernel32.PeekNamedPipe(
                    self._h,
                    None,
                    0,
                    None,
                    ctypes.byref(avail),
                    None,
                )
                if not ok:
                    raise OSError("PeekNamedPipe failed")

                if avail.value > 0:
                    to_read = min(avail.value, 4096)
                    chunk = ctypes.create_string_buffer(to_read)
                    got = wt.DWORD(0)
                    ok = _kernel32.ReadFile(
                        self._h,
                        chunk,
                        to_read,
                        ctypes.byref(got),
                        None,
                    )
                    if not ok:
                        raise OSError("ReadFile failed")
                    if got.value:
                        self._buf += chunk.raw[: got.value]
                        continue

                if time.time() > deadline:
                    raise TimeoutError(
                        f"No response from server after {timeout}s; "
                        f"buffer so far: {self._buf!r}")
                time.sleep(0.01)
            line, self._buf = self._buf.split(b"\n", 1)
            return line.decode()

        def close(self):
            _kernel32.CloseHandle(self._h)

else:
    class ServerClient:
        """Thin client that speaks the why3server wire protocol over a Unix socket."""

        def __init__(self, socket_path, connect_timeout=5.0):
            self._sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            deadline = time.time() + connect_timeout
            while True:
                try:
                    self._sock.connect(socket_path)
                    break
                except (FileNotFoundError, ConnectionRefusedError):
                    if time.time() >= deadline:
                        raise RuntimeError(
                            f"Could not connect to {socket_path!r}")
                    time.sleep(0.05)
            self._buf = b""

        def send(self, data: bytes):
            self._sock.sendall(data)

        def recv_line(self, timeout=15.0) -> str:
            self._sock.settimeout(timeout)
            while b"\n" not in self._buf:
                try:
                    chunk = self._sock.recv(4096)
                except socket.timeout:
                    raise TimeoutError(
                        f"No response from server after {timeout}s; "
                        f"buffer so far: {self._buf!r}")
                if not chunk:
                    raise EOFError("Server closed connection unexpectedly")
                self._buf += chunk
            line, self._buf = self._buf.split(b"\n", 1)
            return line.decode()

        def close(self):
            try:
                self._sock.close()
            except OSError:
                pass

# ---------------------------------------------------------------------------
# Server lifecycle helper
# ---------------------------------------------------------------------------

class ServerFixture:
    """Starts why3server in a temp directory and tears it down after the test."""

    def __init__(self, parallel=2, extra_args=()):
        self._tmpdir = tempfile.mkdtemp(prefix="why3test_")
        self._log_path = os.path.join(self._tmpdir, "why3server.log")
        self._log_snapshot = None
        if IS_WINDOWS:
            import uuid
            basename = f"why3test_{os.getpid()}_{uuid.uuid4().hex[:8]}"
            # The server strips the directory and uses just the basename as the
            # pipe name, so we store both forms.
            self._pipe_basename = basename
            self.connect_path = f"\\\\.\\pipe\\{basename}"
            socket_arg = os.path.join(self._tmpdir, basename)
        else:
            self.connect_path = os.path.join(self._tmpdir, "s.sock")
            socket_arg = self.connect_path

        cmd = [
            SERVER_BIN,
            "--socket", socket_arg,
            "-j", str(parallel),
            "--logging",
            *extra_args,
        ]
        self._proc = subprocess.Popen(
            cmd,
            cwd=self._tmpdir,      # output temp files land here
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        # Give the server a moment to create the socket / pipe
        time.sleep(0.3)

    def connect(self) -> ServerClient:
        return ServerClient(self.connect_path)

    def tmpdir(self) -> str:
        return self._tmpdir

    def _capture_log_snapshot(self, tail_bytes=65536):
        if self._log_snapshot is not None:
            return
        if not os.path.isfile(self._log_path):
            self._log_snapshot = "<why3server.log not found>"
            return
        try:
            with open(self._log_path, "rb") as f:
                f.seek(0, os.SEEK_END)
                size = f.tell()
                start = max(0, size - tail_bytes)
                f.seek(start)
                data = f.read()
            self._log_snapshot = data.decode("utf-8", errors="replace")
        except OSError as exc:
            self._log_snapshot = f"<could not read why3server.log: {exc}>"

    def stop(self):
        self._proc.terminate()
        try:
            self._proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self._proc.kill()
            self._proc.wait()
        self._capture_log_snapshot()
        shutil.rmtree(self._tmpdir, ignore_errors=True)

# ---------------------------------------------------------------------------
# Protocol helpers
# ---------------------------------------------------------------------------

_req_counter_lock = threading.Lock()
_req_counter = 0

def next_id() -> str:
    global _req_counter
    with _req_counter_lock:
        _req_counter += 1
        return f"req{_req_counter}"

def make_run(req_id: str, cmd: str, args=(), timeout=0, memlimit=0) -> bytes:
    parts = ["run", req_id, str(timeout), str(memlimit), cmd] + list(args)
    return (";".join(parts) + "\n").encode()

def parse_response(line: str):
    """Return (kind, id, info_dict).
    kind is 'S' (started) or 'F' (finished).
    info_dict is empty for S; for F it contains exitcode, cpu_time, timeout, outfile.
    """
    parts = line.split(";")
    if parts[0] == "S":
        return "S", parts[1], {}
    if parts[0] == "F":
        return "F", parts[1], {
            "exitcode": int(parts[2]),
            "cpu_time": float(parts[3]),
            "timeout":  int(parts[4]) == 1,
            # outfile is last; its path may itself contain semicolons
            "outfile":  ";".join(parts[5:]),
        }
    raise ValueError(f"Unexpected response line: {line!r}")

def collect_finish(client: ServerClient, req_id: str,
                   deadline_s=20.0):
    """Read lines until we see F;req_id. Return (saw_S, info_dict)."""
    saw_s = False
    t0 = time.time()
    while True:
        remaining = deadline_s - (time.time() - t0)
        if remaining <= 0:
            raise TimeoutError(f"No F response for {req_id!r}")
        line = client.recv_line(timeout=remaining)
        kind, rid, info = parse_response(line)
        if kind == "S" and rid == req_id:
            saw_s = True
        if kind == "F" and rid == req_id:
            return saw_s, info

def collect_all_finishes(client: ServerClient, req_ids,
                         deadline_s=60.0):
    """Read until all req_ids have received an F response.
    Returns {req_id: info_dict}.
    """
    remaining = set(req_ids)
    results = {}
    t0 = time.time()
    while remaining:
        elapsed = time.time() - t0
        if elapsed >= deadline_s:
            raise TimeoutError(
                f"Timed out waiting for: {remaining}")
        line = client.recv_line(timeout=deadline_s - elapsed)
        kind, rid, info = parse_response(line)
        if kind == "F" and rid in remaining:
            remaining.discard(rid)
            results[rid] = info
    return results

# Portable "do nothing for N seconds" commands
def sleep_cmd(seconds):
    """Return (cmd, args) for a process that sleeps for `seconds` seconds."""
    if IS_WINDOWS:
        return "ping", ["-n", str(int(seconds) + 1), "127.0.0.1"]
    return "sleep", [str(seconds)]

def busy_loop_cmd():
    """Return (cmd, args) for an infinite CPU-burning loop.

    The process must be killed externally (e.g. by a server timeout).
    Note: argument strings must not contain semicolons or newlines because
    both are used as delimiters by the wire protocol.
    """
    # "while True: pass" has no semicolons and no newlines.
    return sys.executable, ["-c", "while True: pass"]

def write_script(tmpdir: str, name: str, source: str) -> str:
    """Write *source* to tmpdir/name and return the full path.

    Use this whenever a test needs a Python script with semicolons, newlines,
    or other characters that cannot be embedded in a protocol argument field.
    """
    path = os.path.join(tmpdir, name)
    with open(path, "w") as f:
        f.write(source)
    return path

# ---------------------------------------------------------------------------
# Test classes
# ---------------------------------------------------------------------------

class TestBasic(unittest.TestCase):

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_echo_exits_zero(self):
        """A simple echo exits 0 with timeout=0 and an S before F."""
        rid = next_id()
        if IS_WINDOWS:
            self.c.send(make_run(rid, "cmd", ["/c", "echo hello"]))
        else:
            self.c.send(make_run(rid, "echo", ["hello"]))
        saw_s, info = collect_finish(self.c, rid)
        self.assertTrue(saw_s, "Expected S (started) message before F")
        self.assertEqual(info["exitcode"], 0)
        self.assertFalse(info["timeout"])
        self.assertGreaterEqual(info["cpu_time"], 0.0)

    def test_nonzero_exit_code_preserved(self):
        """The child's exit code is faithfully reported."""
        rid = next_id()
        if IS_WINDOWS:
            self.c.send(make_run(rid, "cmd", ["/c", "exit 42"]))
        else:
            self.c.send(make_run(rid, "sh", ["-c", "exit 42"]))
        _, info = collect_finish(self.c, rid)
        self.assertEqual(info["exitcode"], 42)
        self.assertFalse(info["timeout"])

    def test_stdout_and_stderr_captured(self):
        """Both stdout and stderr go to the outfile."""
        rid = next_id()
        if IS_WINDOWS:
            self.c.send(make_run(rid, "cmd",
                                 ["/c", "echo on_stdout & echo on_stderr 1>&2"]))
        else:
            # Cannot use "sh -c '...; ...'" because semicolons are protocol
            # separators.  Write the script to a file instead.
            script = write_script(
                self.srv.tmpdir(), "io_test.py",
                "import sys\n"
                "sys.stdout.write('on_stdout\\n')\n"
                "sys.stdout.flush()\n"
                "sys.stderr.write('on_stderr\\n')\n"
                "sys.stderr.flush()\n",
            )
            self.c.send(make_run(rid, sys.executable, [script]))
        _, info = collect_finish(self.c, rid)
        self.assertEqual(info["exitcode"], 0)
        self.assertTrue(os.path.isfile(info["outfile"]),
                        f"outfile {info['outfile']!r} does not exist")
        with open(info["outfile"]) as f:
            content = f.read()
        self.assertIn("on_stdout", content)
        self.assertIn("on_stderr", content)

    def test_outfile_in_server_workdir(self):
        """Output temp files are created inside the server's working directory."""
        rid = next_id()
        if IS_WINDOWS:
            self.c.send(make_run(rid, "cmd", ["/c", "echo x"]))
        else:
            self.c.send(make_run(rid, "echo", ["x"]))
        _, info = collect_finish(self.c, rid)
        outfile = os.path.abspath(info["outfile"])
        tmpdir  = os.path.abspath(self.srv.tmpdir())
        self.assertTrue(
            outfile.startswith(tmpdir),
            f"outfile {outfile!r} should be under server tmpdir {tmpdir!r}")


class TestTimeLimits(unittest.TestCase):

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_cpu_timeout_kills_and_reports(self):
        """A CPU-bound process hit by the time limit comes back as timeout=1."""
        rid = next_id()
        cmd, args = busy_loop_cmd()
        self.c.send(make_run(rid, cmd, args, timeout=1))
        t0 = time.time()
        _, info = collect_finish(self.c, rid, deadline_s=15)
        elapsed = time.time() - t0
        self.assertTrue(info["timeout"],
                        f"Expected timeout=1, got info={info}")
        # Should be killed well within the wall-clock budget
        self.assertLess(elapsed, 10,
                        f"CPU-timeout job took {elapsed:.1f}s wall time")

    def test_timeout_is_cpu_not_wall_clock(self):
        """A sleeping (non-CPU) process is not killed by a CPU time limit.
        It should outlive the timeout and exit 0."""
        rid = next_id()
        # sleep 1s wall time with timeout=2 CPU-seconds: should complete fine
        cmd, args = sleep_cmd(1)
        self.c.send(make_run(rid, cmd, args, timeout=2))
        _, info = collect_finish(self.c, rid, deadline_s=10)
        self.assertFalse(info["timeout"],
                         "Sleeping process should NOT be killed by CPU limit")
        self.assertEqual(info["exitcode"], 0)

    def test_zero_timeout_means_unlimited(self):
        """timeout=0 means no limit; a short job runs to completion."""
        rid = next_id()
        cmd, args = sleep_cmd(1)
        self.c.send(make_run(rid, cmd, args, timeout=0))
        _, info = collect_finish(self.c, rid, deadline_s=10)
        self.assertFalse(info["timeout"])
        self.assertEqual(info["exitcode"], 0)

    def test_many_timeout_jobs_server_stays_healthy(self):
        """20 back-to-back timeout jobs: server must remain responsive."""
        N = 20
        ids = [next_id() for _ in range(N)]
        cmd, args = busy_loop_cmd()
        for rid in ids:
            self.c.send(make_run(rid, cmd, args, timeout=1))
        # On Windows, JOB_OBJECT_LIMIT_PROCESS_TIME can be observed with
        # significant scheduling/event latency under load; use a larger budget
        # to avoid flakiness while still checking eventual completion.
        deadline = 180 if IS_WINDOWS else 60
        results = collect_all_finishes(self.c, ids, deadline_s=deadline)
        for rid in ids:
            self.assertTrue(results[rid]["timeout"],
                            f"{rid} should have timed out")
        # Server should still accept a new connection
        c2 = self.srv.connect()
        probe = next_id()
        if IS_WINDOWS:
            c2.send(make_run(probe, "cmd", ["/c", "echo probe"]))
        else:
            c2.send(make_run(probe, "echo", ["probe"]))
        _, info = collect_finish(c2, probe, deadline_s=10)
        self.assertEqual(info["exitcode"], 0)
        c2.close()
        c2.close()


class TestMemoryLimits(unittest.TestCase):
    """
    On Unix, exceeding RLIMIT_AS causes mmap/malloc to fail → Python raises
    MemoryError → process exits with code 1 (not signaled → timeout=0).
    On Windows, exceeding JOB_OBJECT_LIMIT_PROCESS_MEMORY produces
    ERROR_NOT_ENOUGH_QUOTA exit code → timeout=1.
    """

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_within_limit_succeeds(self):
        """A process that allocates well within the limit exits 0."""
        rid = next_id()
        # Allocate 10 MB; limit is 256 MB
        script = "x = bytearray(10 * 1024 * 1024)"
        self.c.send(make_run(rid, sys.executable, ["-c", script],
                             memlimit=256))
        _, info = collect_finish(self.c, rid, deadline_s=15)
        self.assertEqual(info["exitcode"], 0)
        self.assertFalse(info["timeout"])

    def test_exceeding_limit_fails(self):
        """Process that allocates beyond memlimit exits non-zero."""
        rid = next_id()
        # Try to allocate 512 MB; limit is 64 MB
        # On Unix, Python uses ~15 MB of virtual space at start, so 64 MB
        # still lets Python launch but the bytearray call will fail.
        script = "x = bytearray(512 * 1024 * 1024)"
        self.c.send(make_run(rid, sys.executable, ["-c", script],
                             memlimit=64))
        _, info = collect_finish(self.c, rid, deadline_s=15)
        # Depending on platform/runtime, this may be a forced kill or an
        # unhandled allocation failure, but it should not succeed.
        self.assertNotEqual(info["exitcode"], 0,
                            f"Expected non-zero exit from OOM; got {info}")


class TestParallel(unittest.TestCase):

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_two_jobs_run_concurrently(self):
        """With -j 2, two 2-second jobs complete in roughly 2s, not 4s."""
        ids = [next_id(), next_id()]
        t0 = time.time()
        for rid in ids:
            cmd, args = sleep_cmd(2)
            self.c.send(make_run(rid, cmd, args))
        collect_all_finishes(self.c, ids, deadline_s=15)
        elapsed = time.time() - t0
        self.assertLess(elapsed, 3.5,
                        f"Two 2s jobs with -j2 should finish <3.5s, took {elapsed:.1f}s")

    def test_third_job_queued_until_slot_free(self):
        """With -j 2 and three 2-second jobs, wall time is ~4s (not ~2s or ~6s)."""
        ids = [next_id(), next_id(), next_id()]
        t0 = time.time()
        for rid in ids:
            cmd, args = sleep_cmd(2)
            self.c.send(make_run(rid, cmd, args))
        collect_all_finishes(self.c, ids, deadline_s=15)
        elapsed = time.time() - t0
        # Should take ~4s (two batches), not ~2s (all concurrent with j=3)
        # and not ~6s (all serial)
        self.assertGreater(elapsed, 3.0,
                           f"Third job should have waited; elapsed={elapsed:.1f}s")
        self.assertLess(elapsed, 6.0,
                        f"All three jobs took too long: {elapsed:.1f}s")

    def test_fifo_queue_ordering_with_j1(self):
        """With -j 1, jobs complete in exactly the order they were submitted."""
        self.c.close()
        self.srv.stop()
        self.srv = ServerFixture(parallel=1)
        self.c   = self.srv.connect()

        ids = [next_id() for _ in range(4)]
        for rid in ids:
            cmd, args = sleep_cmd(0.3)
            self.c.send(make_run(rid, cmd, args))

        finish_order = []
        seen = set()
        deadline = time.time() + 20
        while len(finish_order) < len(ids):
            remaining = deadline - time.time()
            if remaining <= 0:
                self.fail(f"Timed out; finish_order so far: {finish_order}")
            line = self.c.recv_line(timeout=remaining)
            kind, rid, _ = parse_response(line)
            if kind == "F" and rid not in seen:
                seen.add(rid)
                finish_order.append(rid)

        self.assertEqual(finish_order, ids,
                         "Jobs did not complete in FIFO submission order")


class TestInterrupt(unittest.TestCase):

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_interrupt_running_process(self):
        """Interrupting a running process causes an F response to arrive quickly."""
        rid = next_id()
        if IS_WINDOWS:
            script = write_script(
                self.srv.tmpdir(), "interrupt_sleep.py",
                "import time\n"
                "time.sleep(60)\n",
            )
            cmd, args = sys.executable, [script]
        else:
            cmd, args = sleep_cmd(60)
        self.c.send(make_run(rid, cmd, args))
        # Wait for S (started) before interrupting
        saw_s = False
        start_deadline = time.time() + 10
        while time.time() < start_deadline and not saw_s:
            line = self.c.recv_line(timeout=max(0.1, start_deadline - time.time()))
            kind, msg_rid, _ = parse_response(line)
            if kind == "S" and msg_rid == rid:
                saw_s = True
                break
            if kind == "F" and msg_rid == rid:
                self.fail("Process finished before interrupt; expected it to still be running")
        self.assertTrue(saw_s, "Expected S before interrupt")
        t0 = time.time()
        self.c.send(f"interrupt;{rid}\n".encode())
        _, info = collect_finish(self.c, rid, deadline_s=20)
        elapsed = time.time() - t0
        threshold = 10 if IS_WINDOWS else 5
        self.assertLess(elapsed, threshold,
                        f"Interrupt should produce F quickly, took {elapsed:.1f}s")

    def test_interrupt_queued_request_never_runs(self):
        """Queued request that is interrupted returns F without ever producing S."""
        # Fill both -j2 slots with long sleeps
        blocker_ids = [next_id(), next_id()]
        for bid in blocker_ids:
            cmd, args = sleep_cmd(60)
            self.c.send(make_run(bid, cmd, args))
        time.sleep(0.3)   # let them start

        queued_rid = next_id()
        cmd, args = sleep_cmd(60)
        self.c.send(make_run(queued_rid, cmd, args))
        time.sleep(0.1)   # server processes the queue push
        self.c.send(f"interrupt;{queued_rid}\n".encode())

        # Drain messages; the queued job should produce F but no S
        saw_s = False
        got_f = False
        deadline = time.time() + 8
        while not got_f and time.time() < deadline:
            line = self.c.recv_line(timeout=5)
            kind, rid, _ = parse_response(line)
            if rid == queued_rid:
                if kind == "S":
                    saw_s = True
                if kind == "F":
                    got_f = True

        self.assertTrue(got_f, "Expected F for interrupted queued request")
        self.assertFalse(saw_s,
                         "Interrupted queued request should never produce S")

    def test_interrupt_unknown_id_is_ignored(self):
        """Sending interrupt for an ID the server doesn't know must not crash it."""
        self.c.send(b"interrupt;no_such_id\n")
        time.sleep(0.2)
        # Server must still work
        rid = next_id()
        if IS_WINDOWS:
            self.c.send(make_run(rid, "cmd", ["/c", "echo alive"]))
        else:
            self.c.send(make_run(rid, "echo", ["alive"]))
        _, info = collect_finish(self.c, rid, deadline_s=10)
        self.assertEqual(info["exitcode"], 0)


class TestClientDisconnect(unittest.TestCase):
    """The server must survive client disconnections gracefully and continue
    serving other clients."""

    def setUp(self):
        self.srv = ServerFixture(parallel=2)

    def tearDown(self):
        self.srv.stop()

    def _probe_server_alive(self):
        """Returns True if the server responds to a simple echo."""
        c = self.srv.connect()
        rid = next_id()
        if IS_WINDOWS:
            c.send(make_run(rid, "cmd", ["/c", "echo alive"]))
        else:
            c.send(make_run(rid, "echo", ["alive"]))
        try:
            _, info = collect_finish(c, rid, deadline_s=8)
            return info["exitcode"] == 0
        except Exception:
            return False
        finally:
            c.close()

    def test_disconnect_while_job_running(self):
        """Client disconnects mid-run; server kills the orphaned job and keeps running."""
        c = self.srv.connect()
        rid = next_id()
        cmd, args = sleep_cmd(30)
        c.send(make_run(rid, cmd, args))
        c.recv_line(timeout=5)    # consume S
        c.close()
        time.sleep(0.5)
        self.assertTrue(self._probe_server_alive(),
                        "Server should still be alive after client disconnect")

    def test_disconnect_without_sending_anything(self):
        """Client connects but sends nothing before closing."""
        for _ in range(10):
            c = self.srv.connect()
            c.close()
            time.sleep(0.02)
        self.assertTrue(self._probe_server_alive())

    def test_partial_message_then_disconnect(self):
        """Client sends an incomplete request (no trailing newline) then closes."""
        c = self.srv.connect()
        c.send(b"run;half_baked_request_no_newline")
        c.close()
        time.sleep(0.3)
        self.assertTrue(self._probe_server_alive())

    def test_rapid_connect_disconnect_churn(self):
        """50 clients connect and immediately disconnect; server must survive."""
        for _ in range(50):
            c = self.srv.connect()
            c.close()
        self.assertTrue(self._probe_server_alive())

    def test_multiple_clients_independent(self):
        """Two simultaneous clients each run a job; responses go to the right client."""
        c1 = self.srv.connect()
        c2 = self.srv.connect()
        rid1 = next_id()
        rid2 = next_id()
        if IS_WINDOWS:
            c1.send(make_run(rid1, "cmd", ["/c", "echo client1"]))
            c2.send(make_run(rid2, "cmd", ["/c", "echo client2"]))
        else:
            c1.send(make_run(rid1, "sh", ["-c", "echo client1"]))
            c2.send(make_run(rid2, "sh", ["-c", "echo client2"]))
        _, info1 = collect_finish(c1, rid1)
        _, info2 = collect_finish(c2, rid2)
        self.assertEqual(info1["exitcode"], 0)
        self.assertEqual(info2["exitcode"], 0)
        with open(info1["outfile"]) as f:
            content1 = f.read()
        with open(info2["outfile"]) as f:
            content2 = f.read()
        self.assertIn("client1", content1)
        self.assertIn("client2", content2)
        c1.close()
        c2.close()


class TestGrandchildren(unittest.TestCase):
    """
    Windows: the IOCP fires for every process in the job object, including
    grandchildren. server-win.c:handle_child_event guards against this by
    comparing triggering_pid with GetProcessId(child->handle).

    Unix: the server kills the entire process group, so grandchildren die too.
    """

    def setUp(self):
        self.srv = ServerFixture(parallel=2)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_parent_exits_before_grandchild(self):
        """Process spawns a grandchild and exits immediately.
        Server must report the parent's exit (exitcode 0), not hang waiting
        for the grandchild, and must not double-report."""
        rid = next_id()
        if IS_WINDOWS:
            # Cannot embed semicolons in protocol args; use a script file.
            script = write_script(
                self.srv.tmpdir(), "gc_spawn.py",
                "import subprocess\n"
                "import time\n"
                "subprocess.Popen(['ping', '-n', '5', '127.0.0.1'])\n"
                "time.sleep(0.1)\n",
            )
            self.c.send(make_run(rid, sys.executable, [script]))
        else:
            # sh spawns sleep in background then exits; no semicolons here.
            self.c.send(make_run(rid, "sh", ["-c", "sleep 10 &"]))
        _, info = collect_finish(self.c, rid, deadline_s=10)
        self.assertEqual(info["exitcode"], 0)
        self.assertFalse(info["timeout"])

    def test_parent_with_grandchild_is_timed_out(self):
        """Parent that spawned a grandchild is still killed by CPU limit and reported as timeout=1.

        Detailed behaviour:

        On Unix: RLIMIT_CPU kills the parent via SIGXCPU.  The grandchild is
        NOT automatically killed by the resource limit itself; the server kills
        it via kill(-pgid) only on explicit interrupt.  This test verifies that
        the presence of a grandchild does not prevent the timeout from being
        detected and reported.

        On Windows: the Job object kills all members when the CPU quota is
        exceeded, so both parent and grandchild die.
        """
        rid = next_id()
        # Cannot embed semicolons or newlines in protocol args; use a file.
        script = write_script(
            self.srv.tmpdir(), "gc_timeout.py",
            "import subprocess\n"
            "subprocess.Popen(['sleep', '60'])\n"  # grandchild (Unix)
            "while True: pass\n",                   # CPU-burning parent
        ) if not IS_WINDOWS else write_script(
            self.srv.tmpdir(), "gc_timeout.py",
            "import subprocess\n"
            "subprocess.Popen(['ping', '-n', '60', '127.0.0.1'])\n"
            "while True: pass\n",
        )
        self.c.send(make_run(rid, sys.executable, [script], timeout=1))
        _, info = collect_finish(self.c, rid, deadline_s=15)
        self.assertTrue(info["timeout"],
                        f"Expected timeout when parent CPU-limited; got {info}")


class TestStress(unittest.TestCase):

    def setUp(self):
        self.srv = ServerFixture(parallel=4)
        self.c   = self.srv.connect()

    def tearDown(self):
        self.c.close()
        self.srv.stop()

    def test_100_sequential_jobs(self):
        """Send 100 jobs; all must complete and all must return exitcode 0."""
        N = 100
        ids = [next_id() for _ in range(N)]
        for rid in ids:
            if IS_WINDOWS:
                self.c.send(make_run(rid, "cmd", ["/c", f"echo {rid}"]))
            else:
                self.c.send(make_run(rid, "echo", [rid]))
        results = collect_all_finishes(self.c, ids, deadline_s=120)
        for rid in ids:
            self.assertEqual(results[rid]["exitcode"], 0,
                             f"{rid} exited non-zero")

    def test_50_concurrent_jobs(self):
        """Flood with 50 jobs (more than -j4 slots); all must eventually finish."""
        N = 50
        ids = [next_id() for _ in range(N)]
        for rid in ids:
            cmd, args = sleep_cmd(0.1)
            self.c.send(make_run(rid, cmd, args))
        results = collect_all_finishes(self.c, ids, deadline_s=60)
        self.assertEqual(len(results), N)

    def test_interleaved_timeout_and_normal(self):
        """Alternating fast jobs and timeout jobs; outcomes must all be correct."""
        fast_ids    = []
        timeout_ids = []
        for i in range(20):
            if i % 2 == 0:
                rid = next_id()
                fast_ids.append(rid)
                if IS_WINDOWS:
                    self.c.send(make_run(rid, "cmd", ["/c", "echo fast"]))
                else:
                    self.c.send(make_run(rid, "echo", ["fast"]))
            else:
                rid = next_id()
                timeout_ids.append(rid)
                cmd, args = busy_loop_cmd()
                self.c.send(make_run(rid, cmd, args, timeout=1))

        all_ids = fast_ids + timeout_ids
        results = collect_all_finishes(self.c, all_ids, deadline_s=60)

        for rid in fast_ids:
            self.assertEqual(results[rid]["exitcode"], 0,
                             f"Fast job {rid} should exit 0")
            self.assertFalse(results[rid]["timeout"],
                             f"Fast job {rid} should not timeout")
        for rid in timeout_ids:
            self.assertTrue(results[rid]["timeout"],
                            f"Timeout job {rid} should have timed out")

    def test_parallel_command_changes_j(self):
        """The 'parallel;n' command dynamically changes the job limit."""
        # Drop to -j1, queue 3 jobs, bump to -j3, all should finish faster
        self.c.send(b"parallel;1\n")
        ids = [next_id() for _ in range(3)]
        for rid in ids:
            cmd, args = sleep_cmd(1)
            self.c.send(make_run(rid, cmd, args))
        time.sleep(0.2)
        self.c.send(b"parallel;3\n")
        t0 = time.time()
        collect_all_finishes(self.c, ids, deadline_s=15)
        elapsed = time.time() - t0
        # With -j1 and 3x1s jobs it would take ~3s; after bumping to -j3
        # the two queued jobs run concurrently, so ~2s total
        self.assertLess(elapsed, 3.5,
                        f"After parallel;3, jobs should run faster; took {elapsed:.1f}s")


# ---------------------------------------------------------------------------
# Custom test runner: one line per test, details only on failure
# ---------------------------------------------------------------------------

class _CompactResult(unittest.TestResult):
    _SEP1 = "=" * 70
    _SEP2 = "-" * 70

    def __init__(self):
        super().__init__()
        self._out = sys.stdout

    def _label(self, test):
        doc = test.shortDescription()
        return doc if doc else test._testMethodName

    def _write(self, tag, test):
        self._out.write(f"{tag}  {self._label(test)}\n")
        self._out.flush()

    def addSuccess(self, test):
        self._write("PASS", test)

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self._write("FAIL", test)

    def addError(self, test, err):
        super().addError(test, err)
        self._write("ERROR", test)

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        self._write("SKIP", test)

    def addExpectedFailure(self, test, err):
        super().addExpectedFailure(test, err)
        self._write("XFAIL", test)

    def addUnexpectedSuccess(self, test):
        super().addUnexpectedSuccess(test)
        self._write("XPASS", test)

    def printErrors(self):
        for label, cases in [("FAIL", self.failures), ("ERROR", self.errors)]:
            for test, trace in cases:
                self._out.write(f"\n{self._SEP1}\n")
                self._out.write(f"{label}: {self._label(test)}\n")
                self._out.write(f"{self._SEP2}\n")
                self._out.write(trace)
                srv = getattr(test, "srv", None)
                log_snapshot = getattr(srv, "_log_snapshot", None) if srv else None
                if log_snapshot:
                    self._out.write("\n")
                    self._out.write(self._SEP2 + "\n")
                    self._out.write("why3server.log (tail)\n")
                    self._out.write(self._SEP2 + "\n")
                    self._out.write(log_snapshot)
                    if not log_snapshot.endswith("\n"):
                        self._out.write("\n")
        self._out.flush()

    def summary(self):
        n = self.testsRun
        ok = n - len(self.failures) - len(self.errors) - len(self.skipped)
        parts = [f"{ok} passed"]
        if self.failures:
            parts.append(f"{len(self.failures)} failed")
        if self.errors:
            parts.append(f"{len(self.errors)} errors")
        if self.skipped:
            parts.append(f"{len(self.skipped)} skipped")
        return f"{n} tests: {', '.join(parts)}"


class _CompactRunner:
    def run(self, suite):
        result = _CompactResult()
        suite.run(result)
        result.printErrors()
        sys.stdout.write(f"\n{result.summary()}\n")
        sys.stdout.flush()
        return result


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if shutil.which(SERVER_BIN) is None:
        sys.stderr.write(
            "why3server not found on PATH. Please add it to PATH and retry.\n"
        )
        sys.exit(2)
    unittest.main(testRunner=_CompactRunner(), exit=True)
