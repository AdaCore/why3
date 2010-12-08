
open Why
open Ident
open Term
open Pgm_types

module Mnm : Map.S with type key = string

type namespace = private {
  ns_pr : psymbol   Mnm.t;  (* program symbols *)
  ns_ex : esymbol   Mnm.t;  (* exception symbols *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

val ns_find_pr : namespace -> string list -> psymbol
val ns_find_ex : namespace -> string list -> esymbol
val ns_find_ns : namespace -> string list -> namespace

(** a module under construction *)
type uc

(** a module *)
type t

val create_module : preid -> uc
val close_module : uc -> t

val open_namespace  : uc -> uc
val close_namespace : uc -> bool -> string option -> uc

(* exceptions *)

exception CloseModule
