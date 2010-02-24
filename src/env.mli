
open Ty
open Term

type t

(** Building *)

val empty : t

type th

val open_theory : t -> string -> th
val close_theory : th -> t

val open_namespace : th -> string -> import:bool -> th
val close_namespace : th -> th

val use_export : th -> string -> th

type th_subst = {
  subst_ts : tysymbol Mts.t;
  subst_fs : fsymbol  Mfs.t;
  subst_ps : psymbol  Mps.t;
}

val clone_export : th -> string -> th_subst -> th

(** Querying *)

type path =
  | Pident of string
  | Pdot of path * string

val find_tysymbol : th -> path -> tysymbol


(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit


(** Debugging *)

val print : Format.formatter -> t -> unit
