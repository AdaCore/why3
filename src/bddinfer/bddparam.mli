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

(** {1 Parametric Binary Decision Diagrams}

    This library is derived from the BDD library by
   J.-C. Filliâtre. It is adapted for being applied in the context of
   abstract interpretation. To do so, it is parameterized by an
   underlying abstract domain. For example, such a parameter could be
   a domain for integer arithmetic.

    Concretely, it expands classical BDDs by allowing more leaves in
   the underlying DAGs: in addition to bottom and top leaves, a leaf
   can be a parameter Fi, intended to denote a state for the parameter
   domain.

    The parameters Fi are only stored in BDDs by unique integers. The
   correspondance between those integers and states from the parameter
   domain must be maintain by the implementation of the parameter
   domain. The operations on the parameter states must be given as a
   module parameter to the [Make] functor below. The underlying module
   parameter must be able to provide a way to perform conjunction of
   two states (meet operation), disjunction (join operation) and
   widening. It should detect top state, bottom states and equivalent
   states as much as possible, so as to optimize the use of BDD.

 *)

type variable = int
    (** A variable is an integer, ranging from 1 to [max_var] (within
        a BDD module). *)

module BddVarMap : Map.S with type key = variable
(** Module providing general-purpose map data structures indexed by
   BDD variables. *)

module type BDD = sig

  (** Number of variables *)

  val get_max_var : unit -> int
    (** Returns the number of variables [max_var].
        Default value is 0, which means that bdds cannot be created
        until the module is initialized using [set_max_var]. *)

  (** The abstract type of BDD nodes *)

  type t


  (** The type of context of states in the parameter domain *)

  type param_context
  (* type param_constraint *)
  type param_state

  (** Accessors *)

 (*
 val var : t -> variable
      (** The root variable of a bdd.
          Convention: [Zero] and [One] have variable [max_var+1] *)

  val low : t -> t
  val high : t -> t
      (** The low and high parts of a bdd, respectively.
          [low] and [high] raise [Invalid_argument] on [Zero] and [One]. *)
*)

  (** Constructors *)

(*
  val zero : t
  val one : t
*)
  val bottom : t
  val top : t

  val make : variable -> low:t -> high:t -> t
    (** Builds a raw bdd node.
        Raises [Invalid_argument] is the variable is out of [1..max_var]. *)

  val mk_var : variable -> t
    (** Builds the bdd reduced to a single variable. *)

  type param_index = int
  (** Indices for states in the parameter domain *)

  val mk_param : param_index -> t
  (** Builds the bdd reduced to the given parameter state. *)

  val mk_not : param_context -> t -> t
  val meet : param_context -> t -> t -> t
  val join : param_context -> t -> t -> t
  val widening : param_context -> t -> t -> t
  (** Builds bdds for negation, conjunction, disjunction, widening *)

  (** change context *)

  val change_ctx : (param_state -> param_state) -> param_context -> t -> param_context -> t
  (** [change_ctx f ctx_src b ctx_dst] produces a bdd in the context
     [ctx_dst], by copying the bdd [b] defined in context [ctx_src]
     and applying [f] to each underlying parametric state *)

  (** renaming *)

  val rename_many :
    (variable -> variable) ->
    (param_state -> param_state) ->
    param_context -> t -> param_context -> t
  (** [rename_many fb fp ctx_src b ctx_dst] produces a BDD in context
     [cts_dst] from BDD [b] of context [ctx_src], by applying the
     renaming function [fb] on Boolean variables, and renaming
     function [fp] on underlying parameter states. [fp] is indeed any
     function that transform a parameter state in context [ctx_src]
     into a parameter state in context [cts_dst], it is not limited to
     renamings, though it should always return a state that is neither
     top nor bottom. *)

  val rename_few :
    (variable * variable) list ->
    (param_state -> param_state) ->
    param_context -> t -> param_context -> t
  (** same as [rename_many] but with better efficiency when the number
     of Boolean variables to rename is small. *)

  (** meet with a constraint in the parameter domain *)

  val meet_with_param_constraint :
    (param_state -> param_state) ->
    param_context -> t -> t


  (** Quantifier elimination *)

  val mk_exist : (variable -> bool) -> param_context -> t -> param_context -> t
  (* val mk_forall : (variable -> bool) -> param_context -> t -> param_context -> t *)
  (** [mk_exists f ctxb b ctx] (resp. [mk_forall f ctxb b ctx])
     quantifies bdd [b] over all variables [v] for which [f v]
     holds. For example: [mk_exists x. x /\ y] produces [y],
     [mk_exists x. x \/ y] produces [one], [mk_forall x. x /\ y]
     produces [zero] and [mk_forall x. x \/ y] produces [y]. [ctxb] is
     the context for [b], whereas [ctx] is the context to use for the
     result. *)

  val extract_known_values : t -> bool BddVarMap.t
  (** [extract_known_values b] returns a map indexed by variables,
     associated to Boolean values.  In that map, a variable [v] is
     associated to [true] (resp. [false]) if bdd [b] entails [v] to
     have this value, that is [b -> v=true] (resp [b -> v=false]) is a
     tautology. *)

  val fold_param_states : (bool -> 'a -> 'a) -> (param_index -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_param_states f g b acc] iterates [g] on each parameter
     state that occur in [b]. It also calls [f b' acc] whenever a leaf
     [top] or [bottom] is met.  *)

  type formula =
  | Ffalse
  | Ftrue
  | Fstate of param_index
  | Fvar of variable
  | Fand of formula * formula
  | For  of formula * formula
  | Fimp of formula * formula
  | Fiff of formula * formula
  | Fnot of formula
  | Fite of formula * formula * formula (* if f1 then f2 else f3 *)

  val as_formula : t -> formula
  (** Builds a propositional formula from the given BDD. The returned
     formula is only build using if-then-else ([Fite]) and variables
     ([Fvar]).  *)

  val as_compact_formula : param_context -> t -> formula
  (** Builds a ``compact'' formula from the given BDD. The returned
     formula is only build using conjunctions, disjunctions,
     variables, negations of variables, and if-then-else where the if
     condition is a variable.  *)

  (** Satisfiability *)

  val is_sat : t -> bool
    (** Checks if a bdd is satisfiable i.e. different from [bottom] *)

  val is_top : t -> bool
    (** Checks if a bdd is a tautology i.e. equal to [top] *)

  val is_bottom : t -> bool
    (** Checks if a bdd is unsatisfiable i.e. equal to [bottom] *)

  val equivalent : t -> t -> bool
    (** Checks if a bdd is equivalent to another bdd *)

  val entails : param_context -> t -> t -> bool
    (** [entails ctx b1 b2] checks that [b1] entails [b2], in other words
        [b1] implies [b2] *)


  (** Pretty printer *)

  val print_var : Format.formatter -> variable -> unit

  val print : Format.formatter -> t -> unit
  (** prints as compound if-then-else expressions *)

  val print_compact : Format.formatter -> t -> unit
  (** prints as Boolean expressions, with fallback to if-then-else
     expressions when nothing is more compact *)

  (** Stats *)

  val stats : unit -> (int * int * int * int * int * int) array
    (** Return statistics on the internal nodes tables (one for each variable).
        The numbers are, in order:
        table length, number of entries, sum of bucket lengths,
        smallest bucket length, median bucket length, biggest bucket length. *)

end

module type VarSig = sig
  val print_var: Format.formatter -> int -> unit
  val size: int
  val max_var: int
end

module type ParamDomain = sig

  type param_index = int
  type param_context
  type param_state

  val meet : param_context -> param_index -> param_index -> param_index option
  val join : param_context -> param_index -> param_index -> param_index option
  val widening : param_context -> param_index -> param_index -> param_index option
  (** when result is [None], it means [bottom] for [meet] and [top]
      for [join] and [widening] *)

  val exist_elim : param_context -> param_index -> param_context -> param_index option
  (** [exist_elim ctxi i ctx] fetches the formula [i] in context
     [ctxi], builds a corresponding formula in context [ctx] and
     returns an index for the result. When result is [None], it means
     [top]. The target context [ctx] is supposed to be a sub-context
     of [ctxi], so that this operation corresponds to existential
     elimination of variables of [ctxi] that are not in [ctx]. *)

  val entails : param_context -> param_index -> param_index -> bool

  val change : (param_state -> param_state) ->
    param_context -> param_index -> param_context  -> param_index
  (** [change f ctx_src i ctx_dst] returns an index in context
     [ctx_dst] for [f s] where [s] is the state of index [i] in
     [ctx_src] *)

  val meet_with_constraint :
    (param_state -> param_state) ->
    param_context -> param_index option -> param_index option

 end

module Make (D: ParamDomain) (_: VarSig) : BDD
  with
    type param_index = D.param_index
   and
   type param_context = D.param_context
   and
   type param_state = D.param_state

(* val make : ?print_var:(Format.formatter -> variable -> unit) ->
   ?size:int -> int -> (module BDD) *) (** Creates a BDD module with a
   given maximum number of variables.  Additionally, the size of the
   internal nodes table for each variable can be specified. Each table
   has a default size (7001) and is resized when necessary (i.e. when
   too many collisions occur).  The [print_var] argument can be used
   to associate names with variables (by default it gives "x1", "x2",
   ...). *)
