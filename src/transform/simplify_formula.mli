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

val fmla_simpl : Term.term -> Term.term

val simplify_formula :  Task.task Trans.trans
val simplify_formula_and_task :  Task.task list Trans.trans

val fmla_remove_quant : keep_model_vars:bool -> Term.term -> Term.term
(** transforms \exists x. x == y /\ F into F[y/x]
    and \forall x. x <> y \/ F into F[y/x]

    if [keep_model_vars] is true, then variables that hold an attribute
    for counterexamples are always kept.
 *)

val simplify_trivial_quantification : Task.task Trans.trans

val simplify_trivial_wp_quantification : Task.task Trans.trans
(** same as [simplify_trivial_quantification] but keep variables that
    hold a counterexample attribute *)

val fmla_cond_subst: (Term.term -> Term.term -> bool) -> Term.term -> Term.term
(** given a formula [f] containing some equality or disequality [t1] ?= [t2]
    such that [filter t1 t2] (resp [filter t2 t1]) evaluates to true,
    [fmla_subst_cond filter f] performs the substitution [t1] -> [t2]
    (resp [t2] -> [t1]) wherever possible and returns an equivalent formula *)
