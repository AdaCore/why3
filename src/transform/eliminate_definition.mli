(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

val eliminate_builtin         : Task.task Trans.trans

val compute_diff :
  (Theory.meta * Theory.meta_arg list) list Trans.trans Trans.trans
(** compute the meta_remove given two tasks one included in the other *)



val eliminate_definition_func : Task.task Trans.trans
val eliminate_definition_pred : Task.task Trans.trans
val eliminate_definition      : Task.task Trans.trans

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
