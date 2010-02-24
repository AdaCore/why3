
open Term

type t

(** Building *)

val create : string list -> t
  (** create an environment for a given loadpath *)

val open_theory : t -> t
val close_theory : t -> string -> t

val open_namespace : t -> t
val close_namespace : t -> string -> t

(** Querying *)

type path =
  | Pident of string
  | Pdot of path * string

val find_tysymbol : path -> t -> tysymbol


(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit


(** Debugging *)

val print : Format.formatter -> t -> unit
