(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

{1 Abstract States}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)


(** {2 Environments} *)

type why_var = private {
    var_name : string;
    unique_tag : int;
  }
(** type of program variables *)

val create_var : string -> why_var

val compare_var : why_var -> why_var -> int

module VarMap : Map.S with type key = why_var

module Bdd = Bddparam

type var_value =
  | UnitValue
  | IntValue of Apron.Var.t
  | RefValue of why_var
  | BoolValue of Bdd.variable
(** type of variable values, which can be either a reference to
   another program variable, an abstract integer variable or an
   abstract Boolean variable *)

type why_env = var_value VarMap.t
(** the type of environments, mapping program variables to abstract
   variables *)

(** {2 States} *)

type t
(** type of abstract states. Such a state holds both a environment and
   abstract values representing constraints over abstract variables. A
   abstract state represent the colletion of concrete program states
   for which those constraints are satisfied *)

val why_env : t -> why_env
(** [why_env s] returns the environment stored by [s] *)

(** {2 Modification of state environnement} *)

type memo_add_env

val add_in_environment : memo_add_env option ref -> t -> why_env -> t
(** [add_in_environment s env] returns a state equivalent to [s] with
   extra variables from [env] added. Raises a failure if some
   variables of [env] are already present in [s].  *)

val restrict_environment : t -> t -> t
(** [restrict_environment s s'] reduces the state [s] to the
   variables that are present in [s']. *)

(** Handling of an havoc statement, that modifies a set of variables
   non-deterministically, following a post-condition.  See usage in
   [Infer], interpretation of [Shavoc].  *)

type memo_havoc

val prepare_havoc : memo_havoc option ref -> var_value VarMap.t -> t -> t * why_env
(** [prepare_havoc memo vars state] returns a pair [res,old]. [vars]
   must be a map that associate to a given variable [x] a fresh
   abstract variable of the appropriate type. The result state [res]
   is a state with appropriate environment to interpret a
   post-condition. [old] is an environment that maps the variables of
   [vars] to their current values, to be used as the old values for
   havoc.  *)

(** {2 State operations} *)

val is_bottom : t -> bool
(** [is_bottom s] is true when [s] represents an empty set of program
   states *)

val is_eq : t -> t -> bool
(** [is_eq s1 s2] is true when [s1] and [s2] represent identical sets
   of program states *)

val is_leq : t -> t -> bool
(** [is_leq s1 s2] is true when [s1] represents a subset of the
   program states represented by [s2] *)



val top : t -> t
(** [top s] is the state in the same context as [s] accepting all values *)

val top_new_ctx : why_env -> t
(** [top_new_ctx env] is the state over [env] accepting all values *)

val bottom : t -> t
(** [bottom s] is the state in the same context as [s] accepting no values *)

val singleton_boolean_var_true : t -> Bdd.variable -> t
(** [singleton_boolean_var_true s v] represents the simple state where
   [v] is true, in the same context as [s] *)

val meet_with_apron_constraint : t -> Apron.Tcons1.t -> t
(** [meet_with_apron_constraint s c] returns a fonction that meets a
   given apron state to the given constraint [c] *)

val join : t -> t -> t
(** [join s1 s2] represents a set that includes the union of states
   represented by [s1] and [s2] *)

val meet : t -> t -> t
(** [meet s1 s2] represents the intersection of states represented by
   [s1] and [s2] *)

val widening : t -> t -> t
(** [widening s1 s2] denotes a *widening* operation from [s1] to [s2].
   [s1] should be included in [s2].  *)

val complement : t -> t
(** [complement s] represents the complement of states represented by
   [s]. *)

(** Deal with the integer part of the state (via Apron) *)

val fresh_apron_var : unit -> Apron.Var.t

val of_apron_expr : t -> Apron.Texpr1.expr -> Apron.Texpr1.t

(** Deal with the Boolean part of the state (via BDD) *)

val fresh_bdd_var : unit -> Bdd.variable

val reset_fresh_var_generators : unit -> unit

module B : Bddparam.BDD

val bdd_stats : unit -> int * (int * int * int * int * int * int) array
(** returns statistics on the usage of BDDs. The first number is the
   next free variable, the second is the collection of statistics from
   the [Bdd] module itself (see [bdd.mli]). *)

(** Printing *)

val print : Format.formatter -> t -> unit

val print_var : Format.formatter -> why_var -> unit

val print_var_value : Format.formatter -> var_value -> unit

val print_env : Format.formatter -> why_env -> unit

(** Conversion of states to formulas *)

module ApronVarMap : Map.S with type key = Apron.Var.t

val invert_varmap_int : t -> why_var ApronVarMap.t

val invert_varmap_bool : t -> why_var Bdd.BddVarMap.t

type linear_constraint =
  Apron.Lincons0.typ * (ApronVarMap.key option * Z.t) list *
   (ApronVarMap.key option * Z.t) list

val as_formula : t -> B.formula * linear_constraint list Wstdlib.Mint.t

(** {2 domains} *)

type bool_domain = BDtrue | BDfalse | BDtop

type int_domain = { id_min : Z.t option ; id_max : Z.t option }

type domain = Bool_domain of bool_domain | Int_domain of int_domain

val print_domain : Format.formatter -> domain -> unit

val print_domains : Format.formatter -> domain VarMap.t -> unit

val get_domains : t -> domain VarMap.t

(** statistics *)

val time_in_meet_with_param_constraint : float ref
val time_in_meet_with_apron_constraint : float ref
val time_in_is_leq : float ref
val time_in_join : float ref
val time_in_meet : float ref
val time_in_widening : float ref
val time_in_add_in_environment : float ref
val time_in_restrict_environment : float ref
val time_in_prepare_havoc : float ref
