(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Processing of jobs using Isabelle server
    main author: Stefan Berghofer <stefan.berghofer@secunet.com>
*)

open Why3

type command =
  | Start_Session of string
  | Stop_Session
  | Use_Theory of string

let dirs_opt = ref ([] : string list)
let include_opt = ref ([] : string list)
let command_opt = ref (None : command option)
let check_limit_opt = ref 10

let recv_buf : Buffer.t = Buffer.create 1024
let recv_buf_idx = ref 0

(* taken from driver/prove_client.ml *)
let send_request_string sock msg =
  let to_write = String.length msg in
  let rec write pointer =
    if pointer < to_write then
      let written = Unix.write_substring sock msg pointer (to_write - pointer) in
      write (pointer + written)
  in write 0

let read_from_server sock =
  let buf = Bytes.make 1024 ' ' in
  let read = Unix.read sock buf 0 1024 in
  Bytes.sub_string buf 0 read

let rec read_line sock =
  let s = Buffer.sub recv_buf
    (!recv_buf_idx) (Buffer.length recv_buf - !recv_buf_idx) in
  try
    let i = String.index s '\n' in
    recv_buf_idx := !recv_buf_idx + i + 1;
    if !recv_buf_idx = Buffer.length recv_buf then
      begin
        recv_buf_idx := 0;
        Buffer.clear recv_buf
      end;
    String.sub s 0 i
  with
    Not_found ->
      Buffer.add_string recv_buf (read_from_server sock);
      read_line sock

(* taken from session/json_util.ml *)
let parse_json_object (s: string) =
  Json_parser.value Json_lexer.read (Lexing.from_string s)

let decode_yxml s =
  let buf = Buffer.create 1024 in
  List.iter
    (function [s] -> Buffer.add_string buf s | _ -> ())
    (List.map (Strings.split '\006') (Strings.split '\005' s));
  Buffer.contents buf

let parse_answer s =
  match Strings.bounded_split ' ' s 2 with
  | [head] -> (head, Json_base.Null)
  | [head; rest] -> (head, parse_json_object rest)
  | _ -> ("???" ^ s, Json_base.Null)

let string_of_json json =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  Json_base.print_json fmt json;
  Format.pp_print_flush fmt ();
  String.map (fun c -> if c = '\n' then ' ' else c) (Buffer.contents buf)

let rec wait_for_msg sock f =
  try
    match f (parse_answer (read_line sock)) with
    | None -> wait_for_msg sock f
    | Some m -> m
  with Unix.Unix_error _ ->
    wait_for_msg sock f

let make_string_list xs =
  Json_base.List (List.map (fun s -> Json_base.String s) xs)

let get_string_field r s =
  Json_base.get_string (Json_base.get_field r s)

let get_message r =
  (get_string_field r "kind", get_string_field r "message")

let get_messages s r =
  List.map get_message (Json_base.get_list (Json_base.get_field r s))

let prefix_of_kind kind = match kind with
  | "writeln" -> ""
  | "error" -> "*** "
  | "warning" -> "### "
  | _ -> "??? "

let print_message (kind, msg) =
  let prfx = prefix_of_kind kind in
  List.iter (fun s -> Format.printf "%s%s\n" prfx s)
    (Strings.split '\n' (decode_yxml msg))

let current_task = ref (None : (Unix.file_descr * string) option)

let handle_interrupt _ =
  match !current_task with
  | None -> ()
  | Some (sock, task) ->
      send_request_string sock
        ("cancel " ^ string_of_json
           (Json_base.Record (Json_base.convert_record
              [("task", Json_base.String task)])) ^ "\n")

let session_start sock session dirs include_sessions =
  send_request_string sock
    ("session_start " ^ string_of_json
       (Json_base.Record (Json_base.convert_record
          ([("session", Json_base.String session)] @
           (if dirs = [] then []
            else [("dirs", make_string_list dirs)]) @
           (if include_sessions = [] then []
            else [("include_sessions", make_string_list include_sessions)])))) ^ "\n");
  let task = wait_for_msg sock
    (function
       ("OK", r) -> Some (get_string_field r "task")
     | _ -> None) in
  current_task := Some (sock, task);
  wait_for_msg sock
    (function
       ("FINISHED", r) ->
         if get_string_field r "task" = task then
           begin
             Format.printf "%s\n" (get_string_field r "session_id");
             Some 0
           end
         else None
     | ("FAILED", r) ->
         if get_string_field r "task" = task then
           begin
             print_message (get_message r);
             Some 2
           end
         else None
     | _ -> None)

let session_stop sock session_id =
  send_request_string sock
    ("session_stop " ^ string_of_json
       (Json_base.Record (Json_base.convert_record
          [("session_id", Json_base.String session_id)])) ^ "\n");
  let task = wait_for_msg sock
    (function
       ("OK", r) -> Some (get_string_field r "task")
     | _ -> None) in
  current_task := Some (sock, task);
  wait_for_msg sock
    (function
       ("FINISHED", r) ->
         if get_string_field r "task" = task then Some 0
         else None
     | ("FAILED", r) ->
         if get_string_field r "task" = task then
           begin
             print_message (get_message r);
             Some 2
           end
         else None
     | _ -> None)

let is_consolidated nodes =
  List.for_all (fun r ->
    Json_base.get_bool (Json_base.get_field
      (Json_base.get_field r "status") "consolidated")) nodes

let base_name s =
  let xs = Strings.split '/' s in
  List.nth xs (List.length xs - 1)

let use_theory sock session_id thy =
  send_request_string sock
    ("use_theories " ^ string_of_json
       (Json_base.Record (Json_base.convert_record
          [("session_id", Json_base.String session_id);
           ("theories", Json_base.List [Json_base.String thy]);
           ("check_limit", Json_base.Int (!check_limit_opt))])) ^ "\n");
  let task = wait_for_msg sock
    (function
       ("OK", r) -> Some (get_string_field r "task")
     | _ -> None) in
  current_task := Some (sock, task);
  wait_for_msg sock
    (function
       ("FINISHED", r) ->
         if get_string_field r "task" = task then
           let nodes = Json_base.get_list (Json_base.get_field r "nodes") in
           let is_consolidated = is_consolidated nodes in
           Some
             (is_consolidated,
              get_messages "errors" r,
              if is_consolidated then
                List.concat (List.map (get_messages "messages") (List.find_all
                  (fun r -> base_name (get_string_field r "node_name") = base_name thy ^ ".thy")
                  nodes))
              else [])
         else None
     | ("FAILED", r) ->
         if get_string_field r "task" = task then
           Some (false, [get_message r], [])
         else None
     | _ -> None)

let purge_theory sock session_id thy =
  send_request_string sock
    ("purge_theories " ^ string_of_json
       (Json_base.Record (Json_base.convert_record
          [("session_id", Json_base.String session_id);
           ("theories", Json_base.List [Json_base.String thy])])) ^ "\n");
  wait_for_msg sock
    (function
       ("OK", _) -> Some ()
     | _ -> None)

let rec use_theory_retry sock session_id thy =
  let (is_consolidated, errs, msgs) = use_theory sock session_id thy in
  if is_consolidated || errs <> [] then
  begin
    purge_theory sock session_id thy;
    List.iter print_message errs;
    List.iter print_message msgs;
    if errs = [] then 0 else 2
  end
  else use_theory_retry sock session_id thy

let _ =
  Arg.parse
    [("-d", Arg.String (fun s -> dirs_opt := !dirs_opt @ [s]), "include session directory");
     ("-i", Arg.String (fun s -> include_opt := !include_opt @ [s]), "include session");
     ("-l", Arg.Int (fun i -> check_limit_opt := i), "set check limit");
     ("-s", Arg.String (fun s -> command_opt := Some (Start_Session s)), "start session");
     ("-x", Arg.Unit (fun () -> command_opt := Some Stop_Session), "stop session");
     ("-t", Arg.String (fun s -> command_opt := Some (Use_Theory s)), "use theory")]
    (fun s -> Format.printf "Bad option: %s\n" s; exit 2)
    "Send request to Isabelle server";
  try
    let address = Unix.inet_addr_of_string (Sys.getenv "ISABELLE_ADDRESS") in
    let port = int_of_string (Sys.getenv "ISABELLE_PORT") in
    let password = Sys.getenv "ISABELLE_PASSWORD" in
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_INET (address, port));
    send_request_string sock (password ^ "\n");
    wait_for_msg sock (function ("OK", _) -> Some () | _ -> None);
    Sys.set_signal Sys.sigint (Sys.Signal_handle handle_interrupt);
    let ret =
      match !command_opt with
      | Some (Start_Session s) -> session_start sock s (!dirs_opt) (!include_opt)
      | Some Stop_Session ->
          let session_id = Sys.getenv "ISABELLE_SESSION_ID" in
          session_stop sock session_id
      | Some (Use_Theory s) ->
          let session_id = Sys.getenv "ISABELLE_SESSION_ID" in
          use_theory_retry sock session_id s
      | _ ->
          Format.printf "Bad command\n"; 2 in
    Unix.shutdown sock Unix.SHUTDOWN_ALL;
    exit ret
  with
    Not_found ->
      Format.printf "Environment variables not defined\n";
      exit 2
