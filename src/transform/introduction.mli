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

(** {1 Introduction of premises} *)

(** The premises of the goal of a task are introduced in the
    context, e.g

      goal G: forall x:t, f1 -> forall y:u, f2 and f3 -> f4

    becomes

      logic x:t
      axiom H1: f1
      logic y:u
      axiom H2: f2
      axiom H3: f3
      goal G: f4

*)

val intros :
  ?known_map:Decl.known_map -> Decl.prsymbol -> Term.term -> Decl.decl list
 (** [intros ?known_map G f] returns the declarations after introducing
     premises of [goal G : f] *)

val introduce_premises : Task.task Trans.trans
(** [introduce_premises] pushes the universal quantifications, the
   implications and the let bindings of the goal into the context,
   when possible. Example:
   `|- G : forall x:t. p -> let y = u in q`
   becomes
   `constant x:t, H: q, constant y = u |- G : q`

*)

val simplify_intros : Task.task Trans.trans

(** {2 variants dedicated to counterexample generation} *)

val dequantification: Task.task Trans.trans
(** [dequantification] attempts to move quantifications and bindings
   in the context when possible. Example:
   `H: let z:t = v in exists w. r
    |- G : forall x:t. p -> let y:t = u in q`
   becomes
   `constant z:t, constant w:t, H: z = v /\ r, constant x:t, constant y:t
    |- G : p -> y = u -> q `

    Intended to be used by drivers for provers when no
    counterexamples are expected. See also [prepare_for_counterexmp.ml].
 *)

val remove_unused_from_context: Task.task Trans.trans
(** [remove_unused_from_context] removes all the extra symbols that
   where kept for tracing, for the purpose of counterexample
   generation. Intended to be used by drivers for provers when no
   counterexamples are expected.  See also [prepare_for_counterexmp.ml]. *)

val add_filtered_prefix : string -> unit
(** [intros] will push all attributes through variables bindings. Custom
    attributes prefixes to be filtered can be added with this function *)

val add_unique_prefix : string -> unit
(** [intros] will push all attributes through variables bindings. However, we
    don't always want to have two different attributes with the same prefix.
    Custom attributes prefixes (initially ["expl:"] and ["hyp_name:"]) can be
    added with this function. An attribute with a unique prefix will only be
    pushed if an other attribute with the same prefix is not present in the
    subterm. *)
