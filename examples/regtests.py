#!/usr/bin/env python3
import sys
import os
import subprocess
import glob
from pathlib import Path


# --- Configuration & State ---
REPLAYOPT = []
OUTPUTOPT = []
OUTPUTDIR : Path | None = None
ONLYPRINTCMD = False
REGTESTS_MODE = ""
success = 0
total = 0
res = 0
sessions_files = []
shapes_files = []

# --- Argument Parsing ---
args = sys.argv[1:]
while args:
    arg = args.pop(0)
    if arg == "--force":
        REPLAYOPT.append("--force")
    elif arg == "--obsolete-only":
        REPLAYOPT.append("--obsolete-only")
    elif arg == "--ignore-shapes":
        REPLAYOPT.append("--ignore-shapes")
    elif arg == "--prover":
        arg=args.pop(0)
        REPLAYOPT.extend(["--prover", arg])
        OUTPUTOPT.extend(["--filter-prover", arg])
    elif arg == "--reduced-mode":
        REGTESTS_MODE = "REDUCED"
    elif arg == "--examples-mode":
        REGTESTS_MODE = "EXAMPLES"
    elif arg == "--output-mode":
        OUTPUTDIR = Path(args.pop(0)).absolute()
    elif arg == "--only-print-command":
        #Can be used with "| (cd examples; parallel)"
        ONLYPRINTCMD = True
    else:
        print(f"{sys.argv[0]}: Unknown option '{arg}'")
        print(f"This script allows to replay all tests in the directory")
        print(f"usage: {sys.argv[0]} [options]")
        print(f"  --force: force saving session after replay, if when no change")
        print(f"  --obsolete-only: force saving session after replay, if when no change")
        print(f"  --ignore-shapes: pass this option to why3 replay")
        print(f"  --prove <p>: only replay proofs with the given prover. See why3 replay --filter-prover")
        print(f"  --reduced-mode: only replay a few selected examples, for the gitlab CI")
        print(f"  --example-mode: only replay examples and case studies, not all tests")
        print(f"  --output-mode: do not replay, only output the files for provers")
        print(f"  --only-print-command: only print the why3 replay commands")
        sys.exit(2)

ORIGINAL_PWD = Path.cwd()
TMP = ORIGINAL_PWD / "why3regtests.out"
TMPERR = ORIGINAL_PWD / "why3regtests.err"

SCRIPT_DIR = Path(__file__).resolve().parent
os.chdir(SCRIPT_DIR)

def print_info(*args,**dict):
    if not ONLYPRINTCMD:
        print(*args,**dict)

def run_dir(directory, extra_l_opt):
    global success, total, res
    dir_path = Path(directory)

    # Generate the list of sessions
    if REGTESTS_MODE == "REDUCED":
        list_file = dir_path / "reduced_regtests.list"
        if list_file.exists():
            with open(list_file, "r") as f:
                # Equivalent to the sed logic: find non-commented lines
                sessions = []
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        # Extract first word and append path
                        parts = line.split()
                        sessions.append(dir_path / parts[0] / "why3session.xml")
        else:
            sessions = []
    else:
        # Standard glob for all subdirectories
        sessions = [Path(p) for p in glob.glob(str(dir_path / "*" / "why3session.xml"))]

    for f in sessions:
        d = f.parent

        if OUTPUTDIR is None:
            print_info(f"Replaying {d} ... ", end="", flush=True)
            cmd = ["../bin/why3.opt", "replay", "-q"] + REPLAYOPT + extra_l_opt.split() + [str(d)]
        else:
            print_info(f"Exporting {d} ... ", end="", flush=True)
            outdir = OUTPUTDIR / d
            outdir.mkdir(parents=True,exist_ok=True)
            cmd = ["../bin/why3.opt", "session", "output", "--output-dir", outdir ] + OUTPUTOPT + extra_l_opt.split() + [str(d)]

        if ONLYPRINTCMD:
            print(*cmd)
            continue

        try:
            with open(TMP, "w") as out_f, open(TMPERR, "w") as err_f:
                result = subprocess.run(cmd, stdout=out_f, stderr=err_f, text=True)

            if result.returncode == 0:
                print("OK", end='', flush=True)
                # Print contents of tmp files if needed
                print(TMP.read_text(), end="")
                print(TMPERR.read_text(), end="")
                success += 1
            else:
                print(f"FAILED (ret code={result.returncode}):", end='', flush=True)
                out_content = TMP.read_text()
                if not out_content.strip():
                    print("standard error: (standard output empty)")
                    print(TMPERR.read_text())
                else:
                    print(out_content)
                res = 1
        except Exception as e:
            print(f"CRITICAL ERROR: {e}")
            res = 1

        total += 1

    # Store for final size summary
    sessions_files.extend(glob.glob(str(dir_path / "*" / "why3session.xml")))
    shapes_files.extend(glob.glob(str(dir_path / "*" / "why3shapes.gz")))

def print_file_stats(label, file_list):
    if not file_list:
        print(f"{label} size : 0 0 0")
        return
    # Emulate 'wc -cl | tail -1'
    total_chars = 0
    total_lines = 0
    for f in file_list:
        p = Path(f)
        if p.exists():
            stats = p.stat()
            total_chars += stats.st_size
            try:
                with open(p, 'rb') as f_obj:
                    total_lines += sum(1 for _ in f_obj)
            except: pass
    print(f"{label:13} size : {total_lines:7} {total_chars:8}")

# --- Main Execution ---
print_info("=== Examples and Case Studies === MUST REPLAY AND ALL GOALS PROVED ===\n")

if REGTESTS_MODE != "":
    print(f"(mode: {REGTESTS_MODE})\n")

run_dir(".", "")
run_dir("micro-c", "")
run_dir("python", "")
run_dir("double_wp", "-L double_wp")
run_dir("avl", "-L avl")
run_dir("c_cursor", "-L c_cursor")
run_dir("foveoos11-cm", "")
run_dir("vacid_0_binary_heaps", "-L vacid_0_binary_heaps")
run_dir("verifythis_2016_matrix_multiplication", "-L verifythis_2016_matrix_multiplication")
run_dir("WP_revisited", "")
run_dir("prover", "-L prover --warn-off=unused_variable")
run_dir("multiprecision", "-L multiprecision")
run_dir("numeric", "")

print_info(f"\nScore on Examples and Case Studies: {success}/{total}\n")

if REGTESTS_MODE == "":
    print_info("=== Standard Library ===\n")
    run_dir("stdlib", "")
    print_info("\n=== Tests ===\n")
    run_dir("tests-provers", "")
    print_info("\n=== Check Builtin translation ===\n")
    run_dir("check-builtin", "")
    print_info("\n=== BTS ===\n")
    run_dir("bts", "")
    print_info("\n=== Logic ===\n")
    run_dir("logic", "")
    run_dir("bitvectors", "-L bitvectors")
    print_info("\n=== MLCFG ===\n")
    run_dir("mlcfg", "")

if not ONLYPRINTCMD:
    print(f"Summary       : {success}/{total}")
    print_file_stats("Sessions", sessions_files)
    print_file_stats("Shapes", shapes_files)

sys.exit(res)
