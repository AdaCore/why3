(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let socket : Unix.file_descr option ref = ref None

exception NotConnected
exception AlreadyConnected
exception InvalidAnswer of string

let is_connected () = !socket <> None

let client_connect ~fail socket_name =
  if !socket <> None then raise AlreadyConnected;
  try
    let sock =
      if Sys.os_type = "Win32" then
        let name = "\\\\.\\pipe\\" ^ socket_name in
        Unix.openfile name [Unix.O_RDWR] 0
      else
      let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
      Unix.connect sock (Unix.ADDR_UNIX socket_name);
      sock
    in
    socket := Some sock
  with
  | Unix.Unix_error(err, func, arg) when fail ->
     Format.eprintf "client_connect: connection failed: %s (%s,%s) (socket_name=%s)@." (Unix.error_message err) func arg socket_name;
     exit 2
  | e when fail ->
     Format.eprintf "client_connect failed for some unexpected reason: %s@\nAborting.@."
                    (Printexc.to_string e);
     exit 2

let client_disconnect () =
  match !socket with
  | None -> raise NotConnected
  | Some sock ->
      socket := None;
      if Sys.os_type <> "Win32" then
        Unix.shutdown sock Unix.SHUTDOWN_ALL;
      Unix.close sock

let send_request_string msg =
  match !socket with
  | None -> raise NotConnected
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
    | None -> raise NotConnected
    | Some sock ->
        (* we only call read() if we are allowed to block
           or if the socket is ready *)
        let do_read =
          blocking ||
          (let l,_,_ = Unix.select [sock] [] [] 0.0 in l <> [])
        in
        if do_read then
          let read = Unix.read sock buf 0 1024 in
          String.sub buf 0 read
        else ""

(* TODO/FIXME: should we be able to change this setting when
   using an external server? *)
(* TODO/FIXME: this number should be stored server-side and
   consulted via a protocol request, if ever needed. The only
   reason for this reference to be here is to store the config
   setting before the first connection request is issued. *)
let max_running_provers : int ref = ref 1

let set_max_running_provers x =
  if x <= 0 then invalid_arg "Prove_client.set_max_running_provers";
  max_running_provers := x;
  if is_connected () then
    send_request_string ("parallel;" ^ string_of_int x ^ "\n")

let send_buf : Buffer.t = Buffer.create 512
let recv_buf : Buffer.t = Buffer.create 1024

(* FIXME? should we send !max_running_provers once connected? *)
let connect_external socket_name =
  if is_connected () then raise AlreadyConnected;
  Buffer.clear recv_buf;
  client_connect ~fail:true socket_name

let connect_internal () =
  if is_connected () then raise AlreadyConnected;
  Buffer.clear recv_buf;
  let cwd = Unix.getcwd () in
  Unix.chdir (Filename.get_temp_dir_name ());
  let socket_name = (* Filename.concat (Unix.getcwd ())
    ("why3server." ^ string_of_int (Unix.getpid ()) ^ ".sock") *)
    Filename.temp_file "why3server" "sock"
  in
  let exec = Filename.concat Config.libdir "why3server" in
  let pid =
    (* use this version for debugging the C code
    Unix.create_process "valgrind"
    [|"/usr/bin/valgrind";exec; "--socket"; socket_name;
      "--single-client";
      "-j"; string_of_int !max_running_provers|]
    Unix.stdin Unix.stdout Unix.stderr
     *)
    Unix.create_process exec
    [|exec; "--socket"; socket_name;
      "--single-client";
      "-j"; string_of_int !max_running_provers|]
    Unix.stdin Unix.stdout Unix.stderr
  in
  Unix.chdir cwd;
  (* sleep before connecting, or the server will not be ready yet *)
  let rec try_connect n d =
    if n <= 0 then client_connect ~fail:true socket_name else
    try client_connect ~fail:false socket_name with _ ->
      ignore (Unix.select [] [] [] d);
      try_connect (pred n) (d *. 4.0) in
  try_connect 5 0.1; (* 0.1, 0.4, 1.6, 6.4, 25.6 *)
  at_exit (fun () -> (* only if succesfully connected *)
    (try client_disconnect () with NotConnected -> ());
    ignore (Unix.waitpid [] pid))

(* TODO/FIXME: how should we handle disconnect if there are still
   tasks in queue? What are the use cases for disconnect? *)
let disconnect = client_disconnect

(* TODO/FIXME: is this the right place to connect-on-demand? *)
let send_request ~id ~timelimit ~memlimit ~use_stdin ~cmd =
  if not (is_connected ()) then connect_internal ();
  Buffer.clear send_buf;
  let servercommand =
    if use_stdin <> None then "runstdin;" else "run;" in
  Buffer.add_string send_buf servercommand;
  Buffer.add_string send_buf (string_of_int id);
  Buffer.add_char send_buf ';';
  Buffer.add_string send_buf (string_of_int timelimit);
  Buffer.add_char send_buf ';';
  Buffer.add_string send_buf (string_of_int memlimit);
  List.iter (fun x ->
      Buffer.add_char send_buf ';';
      Buffer.add_string send_buf x)
    cmd;
  begin match use_stdin with
  | None -> ()
  | Some s ->
      Buffer.add_char send_buf ';';
      Buffer.add_string send_buf s
  end;
  Buffer.add_char send_buf '\n';
  let s = Buffer.contents send_buf in
  send_request_string s

let rec read_lines blocking =
  let s = read_from_client blocking in
  (* TODO: should we detect and handle EOF here? *)
  if s = "" then [] else
  if String.contains s '\n' then begin
    let s = Buffer.contents recv_buf ^ s in
    Buffer.clear recv_buf;
    let l = Strings.rev_split '\n' s in
    match l with
    | [] -> assert false
    | [x] -> [x]
    | (x::xs) as l ->
      if x = "" then List.rev xs else
      if x.[String.length x - 1] = '\n' then List.rev l
      else begin
        Buffer.add_string recv_buf x;
        List.rev xs
      end
  end else begin
    Buffer.add_string recv_buf s;
    read_lines blocking
  end

type final_answer = {
  id        : int;
  time      : float;
  timeout   : bool;
  out_file  : string;
  exit_code : int64;
}

type answer =
  | Started of int
  | Finished of final_answer

let read_answer s =
  try
    match Strings.split ';' s with
    | "F":: id :: exit_s :: time_s :: timeout_s :: ( (_ :: _) as rest) ->
        (* same trick we use in other parsing code. The file name may contain
           ';'. Luckily, the file name comes last, so we still split on ';',
           and put the pieces back together afterwards *)
        Finished { id = int_of_string id;
          out_file = Strings.join ";" rest;
          time = float_of_string time_s;
          exit_code = Int64.of_string exit_s;
          timeout = (timeout_s = "1"); }
    | "S" :: [id] ->
        Started (int_of_string id)
    | _ ->
        raise (InvalidAnswer s)
  with Failure "int_of_string" ->
    raise (InvalidAnswer s)

let read_answers ~blocking =
  List.map read_answer (List.filter (fun x -> x <> "") (read_lines blocking))

let () = Exn_printer.register (fun fmt exn -> match exn with
  | NotConnected ->
      Format.fprintf fmt "Not connected to the proof server"
  | AlreadyConnected ->
      Format.fprintf fmt "Already connected to the proof server"
  | InvalidAnswer s ->
      Format.fprintf fmt "Invalid server answer: %s" s
  | _ -> raise exn)
