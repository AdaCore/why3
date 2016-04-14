val set_socket_name : string -> unit
val set_max_running_provers : int -> unit

val connect : unit -> unit
val disconnect : unit -> unit

val send_request :
  id:int ->
  timelimit:int ->
  memlimit:int ->
  use_stdin:string option ->
  cmd:string list ->
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
