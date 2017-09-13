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

open Why3.Strings
open Format

let blocking = false

let multiplier = 3

let hexa_digit x =
  if x >= 10 then Char.chr (Char.code 'A' + x - 10)
  else Char.chr (Char.code '0' + x)

let hexa_val conf =
  match conf with
    '0'..'9' -> Char.code conf - Char.code '0'
  | 'a'..'f' -> Char.code conf - Char.code 'a' + 10
  | 'A'..'F' -> Char.code conf - Char.code 'A' + 10
  | _ -> 0

let decode s =
  let rec need_decode i =
    if i < String.length s then
      match s.[i] with
        '%' | '+' -> true
      | _ -> need_decode (succ i)
    else false
  in
  let rec compute_len i i1 =
    if i < String.length s then
      let i =
        match s.[i] with
          '%' when i + 2 < String.length s -> i + 3
        | _ -> succ i
      in
      compute_len i (succ i1)
    else i1
  in
  let rec copy_decode_in s1 i i1 =
    if i < String.length s then
      let i =
        match s.[i] with
          '%' when i + 2 < String.length s ->
            let v = hexa_val s.[i + 1] * 16 + hexa_val s.[i + 2] in
            set s1 i1 (Char.chr v); i + 3
        | '+' -> set s1 i1 ' '; succ i
        | x -> set s1 i1 x; succ i
      in
      copy_decode_in s1 i (succ i1)
    else s1
  in
  let rec strip_heading_and_trailing_spaces s =
    if String.length s > 0 then
      if s.[0] == ' ' then
        strip_heading_and_trailing_spaces
          (String.sub s 1 (String.length s - 1))
      else if s.[String.length s - 1] == ' ' then
        strip_heading_and_trailing_spaces
          (String.sub s 0 (String.length s - 1))
      else s
    else s
  in
  if need_decode 0 then
    let len = compute_len 0 0 in
    let s1 = create len in
    strip_heading_and_trailing_spaces (copy_decode_in s1 0 0)
  else s

let special =
  function
    '\000'..'\031' | '\127'..'\255' | '<' | '>' | '\"' | '#' | '%' | '{' |
    '}' | '|' | '\\' | '^' | '~' | '[' | ']' | '`' | ';' | '/' | '?' | ':' |
    '@' | '=' | '&' ->
      true
  | _ -> false

let encode s =
  let rec need_code i =
    if i < String.length s then
      match s.[i] with
        ' ' -> true
      | x -> if special x then true else need_code (succ i)
    else false
  in
  let rec compute_len i i1 =
    if i < String.length s then
      let i1 = if special s.[i] then i1 + 3 else succ i1 in
      compute_len (succ i) i1
    else i1
  in
  let rec copy_code_in s1 i i1 =
    if i < String.length s then
      let i1 =
        match s.[i] with
          ' ' -> set s1 i1 '+'; succ i1
        | c ->
            if special c then
              begin
                set s1 i1 '%';
                set s1 (i1 + 1) (hexa_digit (Char.code c / 16));
                set s1 (i1 + 2) (hexa_digit (Char.code c mod 16));
                i1 + 3
              end
            else begin set s1 i1 c; succ i1 end
      in
      copy_code_in s1 (succ i) i1
    else s1
  in
  if need_code 0 then
    let len = compute_len 0 0 in copy_code_in (create len) 0 0
  else s

let nl = "\013\010"

let http_header fmt answer =
  let answer = if answer = "" then "200 OK" else answer in
  fprintf fmt "HTTP/1.0 %s%s" answer nl

let print_exc exc =
  match exc with
    Unix.Unix_error (err, fun_name, arg) ->
      prerr_string "\"";
      prerr_string fun_name;
      prerr_string "\" failed";
      if String.length arg > 0 then
        begin prerr_string " on \""; prerr_string arg; prerr_string "\"" end;
      prerr_string ": ";
      prerr_endline (Unix.error_message err)
  | Out_of_memory -> prerr_string "Out of memory\n"
  | Match_failure (file, first_char, last_char) ->
      prerr_string "Pattern matching failed, file ";
      prerr_string file;
      prerr_string ", chars ";
      prerr_int first_char;
      prerr_char '-';
      prerr_int last_char;
      prerr_char '\n'
  | Assert_failure (file, first_char, last_char) ->
      prerr_string "Assertion failed, file ";
      prerr_string file;
      prerr_string ", chars ";
      prerr_int first_char;
      prerr_char '-';
      prerr_int last_char;
      prerr_char '\n'
  | x ->
      prerr_string "Uncaught exception: ";
      prerr_string (Obj.magic (Obj.field (Obj.field (Obj.repr x) 0) 0));
      if Obj.size (Obj.repr x) > 1 then
        begin
          prerr_char '(';
          for i = 1 to Obj.size (Obj.repr x) - 1 do
            if i > 1 then prerr_string ", ";
            let arg = Obj.field (Obj.repr x) i in
            if not (Obj.is_block arg) then prerr_int (Obj.magic arg : int)
            else if Obj.tag arg = 252 then
              begin
                prerr_char '\"';
                prerr_string (Obj.magic arg : string);
                prerr_char '\"'
              end
            else prerr_char '_'
          done;
          prerr_char ')'
        end;
      prerr_char '\n'

let print_err_exc exc = print_exc exc; flush stderr

let case_unsensitive_eq s1 s2 = lowercase s1 = lowercase s2

let rec extract_param name stop_char =
  function
    x :: l ->
      if String.length x >= String.length name &&
         case_unsensitive_eq (String.sub x 0 (String.length name)) name
      then
        let i =
          let rec loop i =
            if i = String.length x then i
            else if x.[i] = stop_char then i
            else loop (i + 1)
          in
          loop (String.length name)
        in
        String.sub x (String.length name) (i - String.length name)
      else extract_param name stop_char l
  | [] -> ""

let buff = ref (create 80)
let store len x =
  if len >= String.length !buff then
    buff := !buff ^ create (String.length !buff);
  set !buff len x;
  succ len
let get_buff len = String.sub !buff 0 len

let get_request strm =
  let rec loop len (strm__ : _ Stream.t) =
    match Stream.peek strm__ with
      Some '\010' ->
        Stream.junk strm__;
        let s = strm__ in
        if len == 0 then [] else let str = get_buff len in str :: loop 0 s
    | Some '\013' -> Stream.junk strm__; loop len strm__
    | Some c -> Stream.junk strm__; loop (store len c) strm__
    | _ -> if len == 0 then [] else [get_buff len]
  in
  loop 0 strm

let get_request_and_content strm =
  let request = get_request strm in
  let content =
    match extract_param "content-length: " ' ' request with
      "" -> ""
    | x ->
        let str = create (int_of_string x) in
        for i = 0 to String.length str - 1 do
          set str i (
            let (strm__ : _ Stream.t) = strm in
            match Stream.peek strm__ with
              Some x -> Stream.junk strm__; x
            | _ -> ' ')
        done;
        str
  in
  request, content

let string_of_sockaddr =
  function
    Unix.ADDR_UNIX s -> s
  | Unix.ADDR_INET (a, _) -> Unix.string_of_inet_addr a
let sockaddr_of_string s = Unix.ADDR_UNIX s

let treat_connection _tmout callback addr fd fmt =
  let (request, contents__) =
    let strm =
      let c = " " in
      Stream.from
        (fun _ -> if Unix.read fd c 0 1 = 1 then Some c.[0] else None)
    in
    get_request_and_content strm
  in
  let (script_name, contents__) =
    match extract_param "GET /" ' ' request with
      "" -> extract_param "POST /" ' ' request, contents__
    | str ->
       try
         let i = String.index str '?' in
         String.sub str 0 i,
         String.sub str (i + 1) (String.length str - i - 1)
       with
         Not_found -> str, ""
  in
  if script_name = "robots.txt" then
    begin
      http_header fmt "";
      fprintf fmt "Content-type: text/plain%s%s" nl nl;
      fprintf fmt "User-Agent: *%s" nl;
      fprintf fmt "Disallow: /%s@." nl;
      eprintf "Robot request@."
    end
  else
    begin try callback (addr, request) script_name contents__ fmt with
          | Unix.Unix_error (Unix.EPIPE, "write", _) -> ()
          | exc -> print_err_exc exc
    end

(* buffer for storing character read on stdin *)
let buf = Bytes.create 256

exception Nothing_to_do

let accept_connection delay callback stdin_callback s =
  (* eprintf "Unix.select...@."; *)
  let (a,_,_) = Unix.select [s;Unix.stdin] [] [] delay in
  (* eprintf " done@."; *)
  if a = [] then raise Nothing_to_do
  else
  List.iter
    (fun a ->
       if a == s then
         let (t, addr) = Unix.accept s in
         eprintf "got a connection@.";
         Unix.setsockopt t Unix.SO_KEEPALIVE true;
         let cleanup () =
           begin try Unix.shutdown t Unix.SHUTDOWN_SEND with
                   _ -> ()
           end;
           begin try Unix.shutdown t Unix.SHUTDOWN_RECEIVE with
                   _ -> ()
           end;
           try Unix.close t with
             _ -> ()
         in
         let oc = Unix.out_channel_of_descr t in
         treat_connection delay callback addr t (formatter_of_out_channel oc);
         close_out oc;
         eprintf "connection treated@.";
         cleanup ()
       else
         if a == Unix.stdin then
           let n = Unix.read Unix.stdin buf 0 256 in
           eprintf "got a stdin input@.";
           stdin_callback (Bytes.sub_string buf 0 (n-1));
           eprintf "stdin treated@.";
           ()
         else assert false) a


(* the private list of functions to call on idle, sorted higher
       priority first. *)
let idle_handler : (int * (unit -> bool)) list ref = ref []

(* [insert_idle_handler p f] inserts [f] as a new function to call
       on idle, with priority [p] *)
let insert_idle_handler p f =
  let rec aux l =
    match l with
    | [] -> [p,f]
    | (p1,_) as hd :: rem ->
       if p > p1 then (p,f) :: l else hd :: aux rem
  in
  idle_handler := aux !idle_handler

(* the private list of functions to call on timeout, sorted on
       earliest trigger time first. *)
let timeout_handler : (float * float * (unit -> bool)) list ref = ref []

(* [insert_timeout_handler ms t f] inserts [f] as a new function to call
       on timeout, with time step of [ms] and first call time as [t] *)
let insert_timeout_handler ms t f =
  let rec aux l =
    match l with
    | [] -> [ms,t,f]
    | (_,t1,_) as hd :: rem ->
       if t < t1 then (ms,t,f) :: l else hd :: aux rem
  in
  timeout_handler := aux !timeout_handler

(* public function to register a task to run on idle *)
let idle ~(prio:int) f = insert_idle_handler prio f

(* public function to register a task to run on timeout *)
let timeout ~ms f =
  assert (ms > 0);
  let ms = float ms /. 1000.0 in
  let time = Unix.gettimeofday () in
  insert_timeout_handler ms (time +. ms) f

let main_loop addr_opt port callback stdin_callback =
  let addr =
    match addr_opt with
      Some addr ->
      begin try Unix.inet_addr_of_string addr with
              Failure _ -> (Unix.gethostbyname addr).Unix.h_addr_list.(0)
      end
    | None -> Unix.inet_addr_any
  in
  let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt s Unix.SO_REUSEADDR true;
  Unix.bind s (Unix.ADDR_INET (addr, port));
  Unix.listen s 4;
  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  let tm = Unix.localtime (Unix.time ()) in
  eprintf "Ready %4d-%02d-%02d %02d:%02d port %d...@."
                 (1900 + tm.Unix.tm_year) (succ tm.Unix.tm_mon) tm.Unix.tm_mday
                 tm.Unix.tm_hour tm.Unix.tm_min port;
  while true do
    (* attempt to run the first timeout handler *)
    let time = Unix.gettimeofday () in
     match !timeout_handler with
     | (ms,t,f) :: rem when t <= time ->
        timeout_handler := rem;
        let b = f () in
        let time = Unix.gettimeofday () in
        if b then insert_timeout_handler ms (ms +. time) f
     | _ ->
           (* no idle handler *)
(*
           eprintf "check connection for a some delay@.";
*)
           let delay =
             match !timeout_handler with
             | [] -> 0.125
             (* 1/8 second by default *)
             | (_,t,_) :: _ -> t -. time
             (* or the time left until the next timeout otherwise *)
           in
           begin
             try accept_connection delay callback stdin_callback s
             with
               | Nothing_to_do ->
                  begin
                    (* attempt to run the first idle handler *)
                    match !idle_handler with
                    | (p,f) :: rem ->
                       idle_handler := rem;
                       let b = f () in
                       if b then insert_idle_handler p f
                    | [] -> ()
                  end
               | Unix.Unix_error (Unix.ECONNRESET, "accept", _) -> ()
               | Unix.Unix_error ((Unix.EBADF | Unix.ENOTSOCK), "accept", _) as x ->
                  raise x
               | e -> eprintf "Anomaly: %a@." Why3.Exn_printer.exn_printer e
           end
     done
