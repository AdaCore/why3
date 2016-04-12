val standalone : bool ref

val set_socket_name : string -> unit
val set_max_running_provers : int -> unit

val connect : unit -> unit

val send_request :
 use_stdin:bool ->
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

val read_answers : blocking:bool -> answer list

val disconnect : unit -> unit
