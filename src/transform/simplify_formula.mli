(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

val fmla_simpl : Term.fmla -> Term.fmla

val simplify_formula :  Task.task Trans.trans
val simplify_formula_and_task :  Task.task list Trans.trans

val fmla_remove_quant : Term.fmla -> Term.fmla
(** transforms \exists x. x == y /\ F into F[y/x]
    and \forall x. x <> y \/ F into F[y/x] *)

val fmla_cond_subst : (Term.term -> Term.term -> bool) ->
  bool -> Term.fmla -> Term.fmla
(** given a formula [f] (with positivity [sign]) containing some equality
    or disequality [t1] ?= [t2] such that [filter t1 t2] evaluates to true,
    [fmla_subst_cond filter sign f] performs the substitution [t1] -> [t2]
    wherever possible and returns an equivalent formula *)
