val set_socket_name : string -> unit

val connect : unit -> unit

val send_request :
 id:int ->
 timelimit:int ->
 memlimit:int ->
 cmd:string list->
  unit

type answer =
  {
    id        : int;
    exit_code : int;
    time      : float;
    timeout   : bool;
    out_file  : string;
  }

val read_answers : unit -> answer list

val disconnect : unit -> unit
