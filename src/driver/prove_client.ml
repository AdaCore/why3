let socket : Unix.file_descr option ref = ref None

let client_connect socket_name =
  if Sys.os_type = "Win32" then begin
    let name = "\\\\.\\pipe\\" ^ socket_name in
    socket := Some (Unix.openfile name [Unix.O_RDWR] 0)
  end else begin
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX socket_name);
    socket := Some sock
  end

let client_disconnect () =
  match !socket with
  | None -> ()
  | Some s ->
      socket := None;
      Unix.close s

let send_request_string msg =
  match !socket with
  | None -> assert false
  | Some sock ->
      let to_write = String.length msg in
      let rec write pointer =
        if pointer < to_write then
          let written = Unix.write sock msg pointer (to_write - pointer) in
          write (pointer + written)
      in write 0

let read_from_client =
  let buf = String.make 1024 ' ' in
  fun blocking ->
    match !socket with
    | None -> assert false
    | Some sock ->
        (* we only call read() if we are allowed to block or if the socket is
           ready *)
        let do_read =
          blocking ||
          (let l,_,_ = Unix.select [sock] [] [] 0.0 in l <> [])
        in
        if do_read then
          let read = Unix.read sock buf 0 1024 in
          String.sub buf 0 read
        else ""

type answer =
  {
    id        : int;
    exit_code : int;
    time      : float;
    timeout   : bool;
    out_file  : string;
  }

let socket_name : string option ref = ref None

let set_socket_name s =
  socket_name := Some s

let max_running_provers : int ref = ref 1

let set_max_running_provers x =
  if x <= 0 then invalid_arg "Prove_client.set_max_running_provers";
  max_running_provers := x;
  if !socket <> None then
    send_request_string ("parallel;" ^ string_of_int x)

let run_server socket_name =
  let exec = Filename.concat Config.libdir "why3server" in
  Unix.create_process exec
    [|exec; "--socket"; socket_name;
      "--single-client";
      "-j"; string_of_int !max_running_provers |]
    Unix.stdin Unix.stdout Unix.stderr

let buf : Buffer.t = Buffer.create 1024

let connect () =
  Buffer.clear buf;
  match !socket_name with
  | Some sname ->
      (* FIXME? should we send !max_running_provers once connected?
         This branch is normally only used for external servers *)
      client_connect sname
  | None ->
      let cwd = Unix.getcwd () in
      Unix.chdir (Filename.get_temp_dir_name ());
      let sname = Filename.concat (Unix.getcwd ())
        ("why3server." ^ string_of_int (Unix.getpid ()) ^ ".sock") in
      let _server_pid = run_server sname in
      Unix.chdir cwd;
      (* sleep is needed before connecting,
         or the server will not be ready yet *)
      ignore (Unix.select [] [] [] 0.1);
      set_socket_name sname;
      client_connect sname

let connect () =
  (* must disconnect first *)
  if !socket = None then connect ()

let disconnect () =
  client_disconnect ()

let send_request ~id ~timelimit ~memlimit ~use_stdin ~cmd =
  connect ();
  let buf = Buffer.create 128 in
  let servercommand = if use_stdin <> None then "runstdin;" else "run;" in
  Buffer.add_string buf servercommand;
  Buffer.add_string buf (string_of_int id);
  Buffer.add_char buf ';';
  Buffer.add_string buf (string_of_int timelimit);
  Buffer.add_char buf ';';
  Buffer.add_string buf (string_of_int memlimit);
  List.iter (fun x ->
      Buffer.add_char buf ';';
      Buffer.add_string buf x)
    cmd;
  begin match use_stdin with
  | None -> ()
  | Some s ->
      Buffer.add_char buf ';';
      Buffer.add_string buf s
  end;
  Buffer.add_char buf '\n';
  let s = Buffer.contents buf in
  send_request_string s

let rec read_lines blocking =
  let s = read_from_client blocking in
  if s = "" then []
  else if String.contains s '\n' then begin
    let s = Buffer.contents buf ^ s in
    Buffer.clear buf;
    let l = Strings.rev_split '\n' s in
    match l with
    | [] -> assert false
    | [x] -> [x]
    | (x::xs) as l ->
      if x = "" then List.rev xs else
      if x.[String.length x - 1] = '\n' then List.rev l
      else begin
        Buffer.add_string buf x;
        List.rev xs
      end
  end else begin
    Buffer.add_string buf s;
    read_lines blocking
  end

let bool_of_timeout_string s =
  if s = "1" then true else false

let read_answer s =
  let l = Strings.split ';' s in
  match l with
  | id :: exit_s :: time_s :: timeout_s :: ( (_ :: _) as rest) ->
      (* same trick we use in other parsing code. The file name may contain
         ';'. Luckily, the file name comes last, so we still split on ';', and
         put the pieces back together afterwards *)
      let out_file = Strings.join ";" rest in
      { id = int_of_string id;
        out_file = out_file;
        time = float_of_string time_s;
        exit_code = int_of_string exit_s;
        timeout = bool_of_timeout_string timeout_s;
      }
  |_  ->
        assert false

let read_answers ~blocking =
  List.map read_answer (List.filter (fun x -> x <> "") (read_lines blocking))
