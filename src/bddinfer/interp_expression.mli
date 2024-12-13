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

(** {1 Translation between expressions and abstract states} *)

val time_in_meet_condition : float ref

val meet_condition :
  old:Abstract.why_env -> Abstract.t -> Ast.condition -> Abstract.t
(** reduce the given state to the subset satisfying the given condition *)

val abstract_state_to_conditions : Abstract.t -> Ast.condition list
(** convert the given state to a set of conditions *)
