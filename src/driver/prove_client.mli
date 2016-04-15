exception NotConnected
exception AlreadyConnected
exception InvalidAnswer of string

val connect_external : string -> unit
val connect_internal : unit -> unit

val disconnect : unit -> unit

val is_connected : unit -> bool

val send_request :
  id:int ->
  timelimit:int ->
  memlimit:int ->
  use_stdin:string option ->
  cmd:string list ->
  unit

type answer = {
  id        : int;
  time      : float;
  timeout   : bool;
  out_file  : string;
  exit_code : int;
}

val read_answers : blocking:bool -> answer list

val set_max_running_provers : int -> unit
