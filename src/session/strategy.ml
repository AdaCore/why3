open Why3

(** {2 User-defined strategies} *)

type instruction =
  | Icall_prover of Whyconf.prover * int * int (** timelimit, memlimit *)
  | Itransform of string * int (** successor state on success *)
  | Igoto of int (** goto state *)

type t = instruction array
