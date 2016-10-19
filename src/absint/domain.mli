open Apron

module type DOMAIN = sig
  type man
  type env = Environment.t
  type t
  val create_manager: unit -> man
  val bottom: man -> env -> t
  val top: man -> env -> t
  val canonicalize: man -> t -> unit
  val is_bottom: man -> t -> bool
  val is_leq: man -> t -> t -> bool
  val join: man -> t -> t -> t
  val join_list: man -> t list -> t
  val widening: man -> t -> t -> t
  val print: Format.formatter -> t -> unit
  val meet_lincons_array: man -> t -> Lincons1.earray -> t
  val forget_array: man -> t -> Var.t array -> bool -> t
  val assign_linexpr: man -> t -> Var.t -> Linexpr1.t -> t option -> t
  val to_term: Env.env -> Pmodule.pmodule -> man -> t -> (Var.t -> Term.term) -> Term.term
end

module Polyhedra: DOMAIN

