(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Introduction of premises *)

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

val intro_attr : Ident.attribute

val intros :
  ?known_map:Decl.known_map -> Decl.prsymbol -> Term.term -> Decl.decl list
 (** [intros ?known_map G f] returns the declarations after introducing
     premises of [goal G : f] *)

val introduce_premises : Task.task Trans.trans

val simplify_intros: Task.task Trans.trans
