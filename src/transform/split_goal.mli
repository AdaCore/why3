(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val stop_split : Ident.label

val split_pos_full : Term.term -> Term.term list
(** [split_pos_full f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 /\ .. /\ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val split_neg_full : Term.term -> Term.term list
(** [split_neg_full f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 \/ .. \/ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val split_pos_right : Term.term -> Term.term list
(** [split_pos_right] works as [split_pos_full] but does not split
 conjunctions under disjunctions and on the left of implications *)

val split_neg_right : Term.term -> Term.term list
(** [split_neg_right] works as [split_neg_full] but does not split
 disjunctions and implications under conjunctions *)

val split_pos_wp : Term.term -> Term.term list
(** [split_pos_wp] works as [split_pos_right] but stops at
 the `[stop_split]' label and removes the label *)

val split_neg_wp : Term.term -> Term.term list
(** [split_neg_wp] works as [split_neg_right] but stops at
 the `[stop_split]' label and removes the label *)

val split_goal_full : Task.task Trans.tlist
val split_all_full : Task.task Trans.tlist
val split_premise_full : Task.task Trans.trans

val split_goal_right : Task.task Trans.tlist
val split_all_right : Task.task Trans.tlist
val split_premise_right : Task.task Trans.trans

val split_goal_wp : Task.task Trans.tlist
val split_all_wp : Task.task Trans.tlist
val split_premise_wp : Task.task Trans.trans

val split_intro : Task.task Trans.tlist
(** [split_intro] is [split_goal_wp] with skolemization and formula separation *)
