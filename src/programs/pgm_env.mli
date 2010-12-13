
open Why
open Pgm_module

type t

val get_env : t -> Env.env

type retrieve_module = t -> string -> in_channel -> Pgm_module.t Mnm.t

val create : Env.env -> retrieve_module -> t

exception ModuleNotFound of string list * string

val find_module : t -> string list -> string -> Pgm_module.t
  (** [find_module e p n] finds the module named [p.n] in environment [e]
      @raise ModuleNotFound if module not present in env [e] *)
