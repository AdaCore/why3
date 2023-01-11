
(**

{1 Abstract States}

*)



(** {2 Environments} *)

type why_var = private {
    var_name : string;
    unique_tag : int;
  }
(** type of program variables *)

val create_var : string -> why_var

module VarMap : Map.S with type key = why_var

type var_value =
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

val apron_env_of_why_env : why_env -> Apron.Environment.t
(** [@deprecated] *)

val apron_env : t -> Apron.Environment.t
(** [@deprecated] *)

(** {2 Modification of state environnement} *)

val add_in_environment : t -> why_env -> t
(** [add_in_environment s env] returns a state equivalent to [s] with
   extra variables from [env] added. Raises a failure if some
   variables of [env] are already present in [s].  *)

val restrict_environment : t -> why_env -> t
(** [restrict_environment s env] reduces the state [s] to the
   variables that are present in the domain of [env]. Note that the
   codomain of [env] is not taken into account. A variable in [env]
   that is not in the environnement of [s] is also ignored. *)


(** Handling of an havoc statement, that modifies a set of variables
   non-deterministically, following a post-condition.  See usage in
   [Infer], interpretation of [Shavoc].  *)

type havoc_data

val prepare_havoc : var_value VarMap.t -> t -> t * why_env * havoc_data
(** [prepare_havoc vars state] returns a triple [res,old,data] [vars]
   must be a map that associate to a given variable [x] a fresh
   abstract variable of the appropriate type. The result state [res]
   is a state with appropriate environment to interpret a
   post-condition. [old] is an environment that maps the variables of
   [vars] to their current values, to be used as the old values for
   havoc.  [data] is an information to suppply to the next function
   [finalize_havoc]. *)

val finalize_havoc : t -> havoc_data -> t
(** [finalize_havoc state data] produces the appropriate final state
   after an havoc. [data] should be the result of previous call to
   [prepare_havoc]. *)


(** {2 State operations} *)

val top : why_env -> t
(** [top env] is the state over [env] accepting all values *)

val bottom : why_env -> t
(** [bottom env] is the state over [env] accepting no values *)

val is_bottom : t -> bool
(** [is_bottom s] is true when [s] represents an empty set of program
   states *)

val is_eq : t -> t -> bool
(** [is_eq s1 s2] is true when [s1] and [s2] represent identical sets
   of program states *)

val is_leq : t -> t -> bool
(** [is_leq s1 s2] is true when [s1] represents a subset of the
   program states represented by [s2] *)

val join : t -> t -> t
(** [join s1 s2] represents a set that includes the union of states
   represented by [s1] and [s2] *)

val meet : t -> t -> t
(** [meet s1 s2] represents the intersection of states represented by
   [s1] and [s2] *)

val widening : t -> t -> t
(** [widening s1 s2] denotes a *widening* operation from [s1] to [s2].
   [s1] should be included in [s2].  *)

(** Deal with the integer part of the state (via Apron) *)

val meet_with_tcons_array : t -> Apron.Environment.t -> Apron.Tcons1.earray -> t

val assign_texpr : t -> Apron.Var.t -> Apron.Texpr1.t -> t

val fresh_apron_var : unit -> Apron.Var.t

(** Deal with the Boolean part of the state (via BDD) *)

val fresh_bdd_var : unit -> Bdd.variable

val reset_fresh_var_generators : unit -> unit

module B : Bdd.BDD

val meet_with_bdd : t -> B.t -> t

val interp_bool_var_intro : t -> why_var -> Bdd.variable -> B.t -> t
(** [interp_bool_var_intro s x v e] interprets Boolean variable
   introduction [let x = e in ...] using [v] as BDD variable to
   represent [x].  Both [x] and [v] are assumed fresh, that is not
   present yet in state [s].  *)

val interp_bool_assign : t -> Bdd.variable -> Bdd.variable -> B.t -> t
(** interprets Boolean variable introduction [v <- e] *)

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

val boolean_substate : t -> B.t
(** extract the BDD underlying the given state *)

val get_lincons : t -> (Apron.Lincons0.typ *
                          (Apron.Var.t option * Z.t) list *
                            (Apron.Var.t option * Z.t) list
                       ) array
(** extract the linear integer constraints underlying the given state
   *)

val of_tcons_array : var_value VarMap.t -> Apron.Tcons1.earray -> t
(** [of_tcons_array env c] converts the integer constraints [c] over
   the environment [env] into an abstract state *)


(** {2 domains} *)

type bool_domain = BDtrue | BDfalse | BDtop

type int_domain = { id_min : Z.t option ; id_max : Z.t option }

type domain = Bool_domain of bool_domain | Int_domain of int_domain

val print_domain : Format.formatter -> domain -> unit

val print_domains : Format.formatter -> domain VarMap.t -> unit

val get_domains : t -> domain VarMap.t
