(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let debug = Debug.register_info_flag "prepare_for_counterexmp"
  ~desc:"Print@ debugging@ messages@ about@ preparing@ the@ task@ \
    for@ getting@ counter-example."

let prepare_for_counterexmp2 _env task =
  if not (Driver.get_counterexmp task) then begin
    (* Counter-example will not be queried, do nothing *)
    Debug.dprintf debug "Not get ce@.";
    task
  end
  else begin
    (* Counter-example will be queried, prepare the task *)
    Debug.dprintf debug "Get ce@.";
    let comp_trans = Trans.seq [
        (* simplify_intros and intro_vc_vars_counterxmp are needed to
           introduce extra variable whose source location is the same
           as the location of the VC. It is never used by Why3 itself,
           but used by the Spark front-end to display short versions
           of counterexamples, with only the values of variables at
           the source line of the VC. It should be investigated
           whether this should be made differently. 
        Introduction.simplify_intros;
        Intro_projections_counterexmp.intro_projections_counterexmp env *)
        Intro_vc_vars_counterexmp.intro_vc_vars_counterexmp
      ]
    in
    Trans.apply comp_trans task
  end

let prepare_for_counterexmp env = Trans.store (prepare_for_counterexmp2 env)

let () = Trans.register_env_transform "prepare_for_counterexmp"
  prepare_for_counterexmp
  ~desc:"Prepare@ the@ task@ for@ querying@ for@ \
    the@ counter-example@ model.@ This@ transformation@ does@ so@ only@ \
    when@ the@ solver@ will@ be@ asked@ for@ the@ counter-example."


let counterexamples_dependent_intros task =
  let trans =
    if not (Driver.get_counterexmp task) then
      begin
        (* Counter-example will not be queried, remove unused symbols,
           both in the context and in the goal *)
        Introduction.remove_unused_from_context;
      end
    else
      begin
        (* Counter-example will be queried, so introduce as much as
           possible *)
        Debug.dprintf debug "Get ce@.";
        Introduction.dequantification
      end
  in
  Trans.apply trans task

let () = Trans.register_transform "counterexamples_dependent_intros"
  (Trans.store counterexamples_dependent_intros)
  ~desc:"Manages the extra CE symbols depending on whether CE are \
         requested or not: either remove them or introduce them in the \
         context."
