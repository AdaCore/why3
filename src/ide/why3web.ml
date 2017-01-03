
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

open Itp_server

module S = Make (Wserver) (P)

open Format

let interp_request args =
  match args with
  | "list-provers" -> (Command_req (root_node,"list-provers"))
  | _ -> invalid_arg "Why3web.interp_request"

open Json

let message_notification n =
  match n with
  | Error s -> Obj ["message_kind",String "Error"; "msg",String s]
  | Open_File_Error s -> Obj ["message_kind",String "Open_File_Error"; "msg", String s]
  | Proof_error(nid,s) -> Obj ["message_kind",String "Proof_error"; "nid", Int nid; "msg", String s]
  | Transf_error(nid,s) -> Obj ["message_kind",String "Transf_error"; "nid", Int nid; "msg", String s]
  | Strat_error(nid,s) -> Obj ["message_kind",String "Strat_error"; "nid", Int nid; "msg", String s]
  | Replay_Info s -> Obj ["message_kind",String "Replay_info"; "msg", String s]
  | Query_Info(nid,s) -> Obj ["message_kind",String "Query_info"; "nid", Int nid; "msg", String s]
  | Query_Error(nid,s) -> Obj ["message_kind",String "Query_error"; "nid", Int nid; "msg", String s]
  | Help s -> Obj ["message_kind",String "Help"; "msg", String s]
  | Information s -> Obj ["message_kind",String "Information"; "msg", String s]
  | Task_Monitor(a,b,c) ->
     Obj ["message_kind",String "Task_Monitor"; "a", Int a; "b", Int b; "c", Int c]

let nodetype t =
  match t with
  | NRoot -> "root"
  | NFile -> "file"
  | NTheory -> "theory"
  | NTransformation -> "transformation"
  | NGoal -> "goal"
  | NProofAttempt -> "proofattempt"

let notification n =
  match n with
  | Node_change(nid,_info) ->
     Obj ["notification",String "Node_change"; "nid", Int nid; "info",String "TODO"]
  | New_node(nid,parent,nt,name) ->
     Obj ["notification",String "New_node"; "nid", Int nid; "parent", Int parent;
          "nodetype", String (nodetype nt); "name",String name]
  | Remove nid ->
     Obj ["notification",String "Remove"; "nid", Int nid]
  | Initialized _ginfo ->
     Obj ["notification",String "Initialized"; "ginfo", String "TODO"]
  | Saved ->
     Obj ["notification",String "Saved"]
  | Message n ->
     Obj ["notification",String "Message"; "msg", message_notification n]
  | Dead s ->
     Obj ["notification",String "Dead"; "msg", String s]
  | Task(nid,_task) ->
     Obj ["notification",String "Task"; "nid", Int nid; "task", String "TODO"]

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
       let n =
         if n = [] then [Obj ["notification",String "None"]]
         else List.map notification n
       in
       Pp.sprintf "%a@." Json.print (Array n)
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
    Queue.iter (fun f -> P.push_request (Itp_server.Open_session_req f)) files;
    S.init_server config env;
    Wserver.main_loop None 6789 handler stdin_handler
