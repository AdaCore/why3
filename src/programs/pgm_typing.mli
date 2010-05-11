
open Why
open Theory

type error

exception Error of error

val report : Format.formatter -> error -> unit

val file : Env.env -> theory_uc -> Pgm_ptree.file -> theory_uc * Pgm_ttree.file
