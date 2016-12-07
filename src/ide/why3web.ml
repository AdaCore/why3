
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
  | "list-provers" -> (Command_req "list-provers", root_node)
  | _ -> invalid_arg "Why3web.interp_request"

let print_message_notification fmt n =
  match n with
  | Proof_error(nid,s) -> ()
  | Transf_error(nid,s) -> ()
  | Strat_error(nid,s) -> ()
  | Replay_Info(s) -> ()
  | Query_Info(nid,s) -> fprintf fmt "kind=\"query_info\", node=\"%d\", text=\"%s\"" nid s
  | Query_Error(nid,s) -> fprintf fmt "kind=\"query_error\", node=\"%d\", text=\"%s\"" nid s
  | Help s -> fprintf fmt "kind=\"help\", text=\"%s\"" s
  | Information s -> fprintf fmt "kind=\"information\", text=\"%s\"" s
  | Task_Monitor(a,b,c) -> ()

let print_notification fmt n =
  match n with
  | Node_change(nid,info) -> ()
  | New_node(nid,nid',nodetype,info) -> ()
  | Remove(nid) -> ()
  | Initialized(ginfo) -> ()
  | Saved -> ()
  | Message n -> fprintf fmt "{ notification=\"message=\"; %a }"
                              print_message_notification n
  | Dead s -> ()
  | Proof_update(nid,status) -> ()
  | Task(nid,task) -> ()

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
       Pp.sprintf "getNotifications: %a@." (Pp.print_list Pp.space print_notification) n
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

let () = Wserver.main_loop None 6789 handler stdin_handler
