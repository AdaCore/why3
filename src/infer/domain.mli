open Apron

module type ABSTRACT_DOMAIN = sig
  type man
  type t
  type env
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
  val push_label: man -> env -> int -> t -> t
  val is_join_precise: man -> t -> t -> t option
end

module type DOMAIN = sig
  include ABSTRACT_DOMAIN with type env = Environment.t
  val meet_lincons_array: man -> t -> Lincons1.earray -> t
  val forget_array: man -> t -> Var.t array -> bool -> t
  val assign_linexpr: man -> t -> Var.t -> Linexpr1.t -> t option -> t
  val to_lincons_array: man -> t -> Lincons1.earray
  val to_term: Env.env -> Decl.known_map * Pdecl.known_map -> man -> t -> (Var.t -> Term.term) -> Term.term
  val get_linexpr: man -> t -> Var.t -> ((Coeff.t * Var.t) list * Coeff.t) option
  val hash: man -> t -> int
  val is_eq: man -> t -> t -> bool
end

module type TERM_DOMAIN = sig
  include ABSTRACT_DOMAIN with type env = unit
  val forget_var: man -> Term.vsymbol -> t -> t
  val forget_term: man -> Term.term -> t -> t
  val forget_region: man -> Ity.region -> unit Ity.Mpv.t -> t -> t
  val meet_term: man -> Term.term -> t -> t
  val add_variable_to_env: man -> Ity.pvsymbol -> unit
  val add_lvariable_to_env: man -> Term.vsymbol -> unit
  val to_term: man -> t -> Term.term
  val make_consistent: man -> t -> t -> t * t
end

module Polyhedra: DOMAIN
module Box: DOMAIN
module Oct: DOMAIN


