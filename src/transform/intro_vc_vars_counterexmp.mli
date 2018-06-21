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

val intro_vc_vars_counterexmp : Task.task Trans.trans
(** Finds the position of the term t_vc that trigger VC and saves this
    position in meta (for smtv2 printer). For every variable v inside
    the term t_vc that triggers VC introduces constant c equal to the
    variable v with the location of t_vc, attribute "model_trace:*",
    and either attribute "model" or "model_projected".

    This means that all variables that should be collected for
    counterexample will marked by model attributes.

    If the term triggering VC is postcondition of a function, appends to
    the attribute "model_trace:*" string "@old" for variables corresponding
    to old values of input arguments and string "@return" for the variable
    corresponding to the return value of the function.

    ------------------------------------------------------------------

    The rationale of this transformation:
    Variables that should be displayed in counterexample are marked
    by model attributes ("model", "model_projected", "model_trace").

    Variables inside the term that triggers VC should be displayed in
    counterexample for that VC. However, many VCs (tasks) can be generated
    for  a signle *.mlw file and only variables in the term that trigger
    the VC (task) that is currently proven should be displayed. That means
    that the process of selecting variables inside the term that triggers
    VC for counterexample cannot be done before the task is processed.
    It is done by this transformation.
*)

val get_location_of_vc : Task.task -> Loc.position option
(** Gets the location of the term that triggers vc.
    This location is collected by transformation intro_vc_vars_counterexmp. *)
