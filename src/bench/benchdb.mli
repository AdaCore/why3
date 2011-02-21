(** run benchs from the database *)

open Why

val db : Whyconf.config -> Env.env -> unit
