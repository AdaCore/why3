
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

end

open Itp_communication
open Itp_server

module S = Make (Wserver) (P)

open Format

let interp_request args =
  let args_list = Strings.split '_' args in
  match args_list with
  | [ "reload" ]  -> Reload_req
  | [ "list-provers" ]  -> Command_req (root_node,"list-provers")
  | "gettask" :: n :: [] -> Get_task (int_of_string n)
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

let spec = Arg.align [
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
    if Queue.is_empty files then
      Whyconf.Args.exit_with_usage spec usage_str;
    Queue.iter (fun f -> P.push_request (Open_session_req f)) files;
    S.init_server config env;
    Wserver.main_loop None 6789 handler stdin_handler
