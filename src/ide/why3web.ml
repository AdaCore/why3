
open Why3

module P = struct


 let notify _ = ()

 let requests = ref []

 let push_request r =
   requests := r :: !requests

 let get_requests () =
   let l = !requests in requests := []; l

end

module S = Itp_server.Make (Wserver) (P)

open Format

let interp_request args =
  match args with
  | "button1" -> (Itp_server.Command_req "list-provers", 0)
  | _ -> invalid_arg "Why3web.interp_request"

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
       let n = Random.int 4 in
       "{ \"kind\": \"Random\", \"value\" = \"" ^ string_of_int n ^ "\" }"
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
