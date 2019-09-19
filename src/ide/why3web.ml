(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

module P = struct

 let notifications = ref []

 let notify n = notifications := n :: ! notifications

 let get_notifications () =
   let l = !notifications in notifications := []; List.rev l

 let requests = ref []

 let push_request r =
   requests := r :: !requests

 let get_requests () =
   let l = !requests in requests := []; List.rev l

 (* print_ext_any just use the argument function here *)
 let print_ext_any print_any fmt t =
   print_any fmt t

end

open Itp_communication
open Itp_server

module S = Make (Wserver) (P)

open Format

(* Decode URI *)
let decode s =
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i <= String.length s -1 do
    (match s.[!i] with
    (* | '+' -> Buffer.add_string b " " *)
    | '%' ->
        begin
          let a = int_of_string ("0x" ^ (String.sub s (!i + 1) 2)) in
          i := !i + 2;
          Buffer.add_char b (char_of_int a);
        end
    | a -> Buffer.add_char b a);
    i := !i + 1;
  done;
  Buffer.contents b

(* TODO make it cleaner and less inefficient with adapted functions *)
let interp_request args =
  match args with
  | args when Strings.has_prefix "reload" args -> Reload_req
  | args when Strings.has_prefix "list-provers" args ->
      Command_req (root_node,"list-provers")
  | args when Strings.has_prefix "command=" args ->
      let com = Strings.remove_prefix "command=" args in
      (match (Strings.bounded_split ',' com 2) with
      | n :: com :: [] ->
          Command_req (int_of_string n, com)
      | _ -> invalid_arg ("Why3web.interp_request '" ^ args ^ "'"))
  | args when Strings.has_prefix "gettask_" args ->
     let c = false in
     let loc = true in
     Get_task (int_of_string (Strings.remove_prefix "gettask_" args),c,loc)
  | _ -> invalid_arg ("Why3web.interp_request '" ^ args ^ "'")

let handle_script s args =
  match s with
  | "request" ->
     begin
       try P.push_request (interp_request args);
           "{ \"request_received\": \"" ^ args ^ "\" }"
       with e ->
         "{ \"request_error\": \"" ^ args ^ "\" ; \"error\": \"" ^
           (Pp.sprintf "%a" Exn_printer.exn_printer e) ^ "\" } "
     end
  | "getNotifications" ->
      let n = P.get_notifications () in
      Pp.sprintf "%a@." Json_util.print_list_notification n
  | _ -> "bad request"

let plist fmt l =
  List.iter  (fun x -> fprintf fmt "'%s'@\n" x) l

let string_of_addr addr =
  match addr with
    | Unix.ADDR_UNIX s -> s
    | Unix.ADDR_INET (ie,i) ->
	(Unix.string_of_inet_addr ie)^":"^string_of_int(i)

let handler (addr,req) script cont fmt =
       eprintf "addr : %s@." (string_of_addr addr);
       eprintf "req: @[%a@]@." plist req;
       eprintf "script: `%s'@." script;
       let cont = decode cont in
       eprintf "cont: `%s'@." cont;
       let ans = handle_script script cont in
       eprintf "answer: `%s'@." ans;
       Wserver.http_header fmt "HTTP/1.0 200 OK";
       fprintf fmt "Access-Control-Allow-Origin: *\n";
       fprintf fmt "\n"; (* end of header *)
       fprintf fmt "%s" ans;
       fprintf fmt "@."

let help () =
  printf "Available commands:@.";
  printf "q : quit@."

let stdin_handler s =
  match s with
    | "?" -> help ()
    | "q" -> exit 0
    | _ -> printf "unknown command '%s'@." s

(************************)
(* parsing command line *)
(************************)

let files : string Queue.t = Queue.create ()

let opt_parser = ref None

let spec = [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
(*
  "-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<file> add file to the project (ignored if it is already there)";
*)
  Termcode.arg_extra_expl_prefix
]

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>]..."
  (Filename.basename Sys.argv.(0))


let () =
    let config, _base_config, env =
      Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str
    in
    let dir =
      try
        Server_utils.get_session_dir ~allow_mkdir:true files
      with Invalid_argument s ->
        Format.eprintf "Error: %s@." s;
        Whyconf.Args.exit_with_usage spec usage_str
    in
    S.init_server config env dir;
    Queue.iter (fun f -> P.push_request (Add_file_req f)) files;
    Wserver.main_loop None 6789 handler stdin_handler
