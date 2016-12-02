
open Why3

module P = struct

 let notify _ = ()

 let get_requests () = []

end

module S = Itp_server.Make (Unix_scheduler.Unix_scheduler) (P)

open Format

let handle_script s args =
  match s with
    | "request" -> "{ \"request\": \"" ^ args ^ "\" }"
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

let () = Wserver.main_loop None 6789 handler
