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

val intros :  Decl.prsymbol -> Term.term -> Decl.decl list
 (** [intros G f] returns the declarations after introducing
     premises of [goal G : f] *)

val introduce_premises : Task.task Trans.trans


(* superseded by split_goal_wp
val split_intro : Task.task Trans.tlist
(** [split_intro] is [split_goal_wp] followed by [introduce_premises] *)
 *)
