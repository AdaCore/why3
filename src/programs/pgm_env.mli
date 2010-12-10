
open Why

type t

val tag : t -> Hashweak.tag

val create : Env.env -> t

exception ModuleNotFound of string list * string

val find_module : t -> string list -> string -> Pgm_module.t
  (** [find_module e p n] finds the module named [p.n] in environment [e]
      @raise ModuleNotFound if module not present in env [e] *)
