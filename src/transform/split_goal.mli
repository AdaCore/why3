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

val split_pos_full : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_pos_full f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 /\ .. /\ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val split_neg_full : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_neg_full f] returns a list [[g1;..;gk]] such that
 [f] is logically equivalent to [g1 \/ .. \/ gk] and the length
 of the resulting list can be exponential wrt the size of [f] *)

val split_pos_right : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_pos_right] works as [split_pos_full] but does not split
 conjunctions under disjunctions and on the left of implications *)

val split_neg_right : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_neg_right] works as [split_neg_full] but does not split
 disjunctions and implications under conjunctions *)

val split_proof_full : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_proof_full f] returns a list of formulas whose conjunction implies f.
    The reverse implication also holds when f does not contain the by/so
    connectives. In this case, [split_proof_full] works as [split_pos_full]
    but stops at the [stop_split] attribute and removes it. *)

val split_proof_right : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_proof_right f] returns a list of formulas whose conjunction
    implies f. The reverse implication also holds when f does not contain
    the by/so connectives. In this case, [split_proof_right] works as
    [split_pos_right] but stops at the [stop_split] attribute and removes it. *)

val split_intro_full : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_intro_full] works as [split_pos_full] but does not respect the
    [asym_split] attribute, stops at the [stop_split] attribute and removes it *)

val split_intro_right : ?known_map:Decl.known_map -> Term.term -> Term.term list
(** [split_intro_right] works as [split_pos_right] but does not respect the
    [asym_split] attribute, stops at the [stop_split] attribute and removes it *)

val split_goal_full : Task.task Trans.tlist
val split_all_full : Task.task Trans.tlist
val split_premise_full : Task.task Trans.trans

val split_goal_right : Task.task Trans.tlist
val split_all_right : Task.task Trans.tlist
val split_premise_right : Task.task Trans.trans
