(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(**************************************************************************)

(** Propositional formulas *)

type variable = int
    (** A variable is an integer, ranging from 1 to [max_var] (within
        a BDD module). *)

module BddVarMap : Map.S with type key = variable
(** Module providing general-purpose map data structures indexed by
   BDD variables. *)

type formula =
  | Ffalse
  | Ftrue
  | Fvar of variable
  | Fand of formula * formula
  | For  of formula * formula
  | Fimp of formula * formula
  | Fiff of formula * formula
  | Fnot of formula
  | Fite of formula * formula * formula (* if f1 then f2 else f3 *)

module type BDD = sig
  (** Binary Decision Diagrams (BDDs) *)

  (** Number of variables *)

  val get_max_var : unit -> int
    (** Returns the number of variables [max_var].
        Default value is 0, which means that bdds cannot be created
        until the module is initialized using [set_max_var]. *)

  (** The abstract type of BDD nodes *)

  type t

  (** View *)

  type view = Zero | One | Node of variable * t (*low*) * t (*high*)

  val view : t -> view
    (** Displays a bdd as a tree. *)

  (** Accessors *)

  val var : t -> variable
      (** The root variable of a bdd.
          Convention: [Zero] and [One] have variable [max_var+1] *)

  val low : t -> t
  val high : t -> t
      (** The low and high parts of a bdd, respectively.
          [low] and [high] raise [Invalid_argument] on [Zero] and [One]. *)

  (** Constructors *)

  val zero : t
  val one : t

  val make : variable -> low:t -> high:t -> t
    (** Builds a bdd node.
        Raises [Invalid_argument] is the variable is out of [1..max_var]. *)

  val mk_var : variable -> t
    (** Builds the bdd reduced to a single variable. *)

  val mk_not : t -> t
  val mk_and : t -> t -> t
  val mk_or : t -> t -> t
  val mk_imp : t -> t -> t
  val mk_iff : t -> t -> t
    (** Builds bdds for negation, conjunction, disjunction, implication,
        and logical equivalence. *)

  (** Quantifier elimination *)

  val mk_exist : (variable -> bool) -> t -> t
  val mk_forall : (variable -> bool) -> t -> t
  (** [mk_exists f b] (resp. [mk_forall f b]) quantifies bdd [b] over
     all variables [v] for which [f v] holds. For example: [mk_exists
     x. x /\ y] produces [y], [mk_exists x. x \/ y] produces [one],
     [mk_forall x. x /\ y] produces [zero] and [mk_forall x. x \/ y]
     produces [y]. See [test/quant_elim.ml]. *)

  val extract_known_values : t -> bool BddVarMap.t
  (** [extract_known_values b] returns a map indexed by variables,
     associated to Boolean values.  In that map, a variable [v] is
     associated to [true] (resp. [false]) if bdd [b] entails [v] to
     have this value, that is [b -> v=true] (resp [b -> v=false]) is a
     tautology. *)

  (** Generic binary operator constructor *)

  val apply : (bool -> bool -> bool) -> t -> t -> t

  val constrain : t -> t -> t
    (** [constrain f g] is the generalized cofactor, sometimes written
        [f ↓ g]. It is defined for any function [g <> false] so that
        [f = (g /\ (f ↓ g)) \/ (~g /\ (f ↓ ~g))]. Setting [g] to a variable [x]
        gives the classical Shannon cofactors:
        [f = (x /\ (f ↓ x)) \/ (~x /\ (f ↓ ~x))].
        For [f' = constrain f g], [f' xs = f xs] if [g xs], the graph of
        [f'] is often simper than that of [f], but not always.
        Note also that [(∃xs, (α ↓ β)(xs)) = (∃xs, (α /\ β)(xs))], but
        [constrain] is, in general, less costly to calculate than [mk_and].
        See, e.g., Raymond 2008,
        "Synchronous program verification with Lustre/Lesar", §7.9. *)

  val restriction : t -> t -> t
    (** For [f' = restriction f g], [f' xs = f xs] if [g xs], and the graph of
        [f'] is a subset of that of [f].
        I.e., [f'] is a smaller version of [f] for input vectors in the
        "care set" [g].
        See, e.g., Raymond 2008,
        "Synchronous program verification with Lustre/Lesar", §7.9. *)

  val restrict : t -> variable -> bool -> t
   (** [restrict t v b] is the bdd for [t[b/v]], that is, [t] where
       variable [v] is assigned the truth value [b]. *)

  val build : formula -> t
    (** Builds a bdd from a propositional formula [f].
        Raises [Invalid_argument] if [f] contains a variable out of
        [1..max_var]. *)

  val as_formula : t -> formula
  (** Builds a propositional formula from the given BDD. The returned
     formula is only build using if-then-else ([Fite]) and variables
     ([Fvar]).  *)

  val as_compact_formula : t -> formula
  (** Builds a ``compact'' formula from the given BDD. The returned
     formula is only build using conjunctions, disjunctions,
     variables, negations of variables, and if-then-else where the if
     condition is a variable.  *)

  (** Satisfiability *)

  val is_sat : t -> bool
    (** Checks if a bdd is satisfiable i.e. different from [zero] *)

  val tautology : t -> bool
    (** Checks if a bdd is a tautology i.e. equal to [one] *)

  val equivalent : t -> t -> bool
    (** Checks if a bdd is equivalent to another bdd *)

  val entails : t -> t -> bool
    (** [entails b1 b2] checks that [b1] entails [b2], in other words
        [b1] implies [b2] *)

  val count_sat_int : t -> int
  val count_sat : t -> Int64.t
    (** Counts the number of different ways to satisfy a bdd. *)

  val any_sat : t -> (variable * bool) list
    (** Returns one truth assignment which satisfies a bdd, if any.
        The result is chosen deterministically.
        Raises [Not_found] if the bdd is [zero] *)

  val random_sat : t -> (variable * bool) list
    (** Returns one truth assignment which satisfies a bdd, if any.
        The result is chosen randomly.
        Raises [Not_found] if the bdd is [zero] *)

  val all_sat : t -> (variable * bool) list list
    (** Returns all truth assignments which satisfy a bdd [b]. *)

  (** Pretty printer *)

  val print_var : Format.formatter -> variable -> unit

  val print : Format.formatter -> t -> unit
  (** prints as compound if-then-else expressions *)

  val print_compact : Format.formatter -> t -> unit
  (** prints as Boolean expressions, with fallback to if-then-else
     expressions when nothing is more compact *)

  val to_dot : t -> string

  val print_to_dot : t -> file:string -> unit

  val display : t -> unit
    (** displays the given bdd using a shell command "dot -Tps <file> | gv -" *)

  (** Stats *)

  val stats : unit -> (int * int * int * int * int * int) array
    (** Return statistics on the internal nodes tables (one for each variable).
        The numbers are, in order:
        table length, number of entries, sum of bucket lengths,
        smallest bucket length, median bucket length, biggest bucket length. *)
end

module Make(X: sig
  val print_var: Format.formatter -> int -> unit
  val size: int
  val max_var: int
end) : BDD

val make : ?print_var:(Format.formatter -> variable -> unit)
           -> ?size:int
           -> int
           -> (module BDD)
    (** Creates a BDD module with a given maximum number of variables.
        Additionally, the size of the internal nodes table for each variable
        can be specified. Each table has a default size (7001) and is
        resized when necessary (i.e. when too many collisions occur).
        The [print_var] argument can be used to associate names with variables
        (by default it gives "x1", "x2", ...). *)
