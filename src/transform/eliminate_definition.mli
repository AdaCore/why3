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

val eliminate_builtin         : Task.task Trans.trans

val compute_diff :
  (Theory.meta * Theory.meta_arg list) list Trans.trans Trans.trans
(** compute the meta_remove given two tasks one included in the other *)


val eliminate_definition_func : Task.task Trans.trans
val eliminate_definition_pred : Task.task Trans.trans
val eliminate_definition      : Task.task Trans.trans
val eliminate_definition_gen : (Term.lsymbol -> bool) -> Task.task Trans.trans

val eliminate_mutual_recursion: Task.task Trans.trans

(** bisection *)

val bisect : (Task.task -> bool) ->
  Task.task -> (Theory.meta * Theory.meta_arg list) list
  (** [bisect test task] return metas that specify the symbols that
      can be removed without making the task invalid for
      the function test. *)

type bisect_step =
| BSdone of (Theory.meta * Theory.meta_arg list) list
| BSstep of Task.task * (bool -> bisect_step)

val bisect_step : Task.task -> bisect_step
(** Same as before but doing it step by step *)
