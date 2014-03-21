external client_connect : string -> unit      = "c_client_connect"
external client_disconnect : unit -> unit     = "c_client_disconnect"
external send_request_string : string -> unit = "c_send_request_string"
external read_from_client : unit -> string    = "c_read_from_client"

type answer =
  {
    id        : int;
    exit_code : int;
    time      : float;
    timeout   : bool;
    out_file  : string;
  }

let socket_name : string ref = ref ""

let set_socket_name s =
  socket_name := s

let buf : Buffer.t = Buffer.create 1024

let connect () =
  Buffer.clear buf;
  client_connect !socket_name

let disconnect () =
  client_disconnect ()

let send_request ~id ~timelimit ~memlimit ~cmd =
  let buf = Buffer.create 128 in
  Buffer.add_string buf (string_of_int id);
  Buffer.add_char buf ';';
  Buffer.add_string buf (string_of_int timelimit);
  Buffer.add_char buf ';';
  Buffer.add_string buf (string_of_int memlimit);
  List.iter (fun x ->
      Buffer.add_char buf ';';
      Buffer.add_string buf x)
    cmd;
  Buffer.add_char buf '\n';
  let s = Buffer.contents buf in
  send_request_string s

let rec read_lines () =
  let s = read_from_client () in
  let ends_with_newline = s.[String.length s - 1] = '\n' in
  if ends_with_newline || String.contains s '\n' then begin
    let s = Buffer.contents buf ^ s in
    Buffer.clear buf;
    let l = Strings.rev_split s '\n' in
    match l with
    | [] -> assert false
    | [x] -> [x]
    | (x::xs) as l ->
      if ends_with_newline then List.rev l
      else begin
        Buffer.add_string buf x;
        List.rev xs
      end
  end else begin
    Buffer.add_string buf s;
    read_lines ()
  end

let bool_of_timeout_string s =
  if s = "1" then true else false

let read_answer s =
  let l = Strings.rev_split s ';' in
  match l with
  | [ out_file ; timeout_s; time_s; exit_s; id ] ->
    { id = int_of_string id;
      out_file = out_file;
      time = float_of_string time_s;
      exit_code = int_of_string exit_s;
      timeout = bool_of_timeout_string timeout_s;
    }
  |_  ->
        assert false

let read_answers () =
  List.map read_answer (List.filter (fun x -> x <> "") (read_lines ()))
