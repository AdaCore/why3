

exception Parse_error of string

val read_channel :
  Env.env -> string list -> string -> in_channel -> Pmodule.pmodule Wstdlib.Mstr.t
(** [read_channel env path file chan] *)
