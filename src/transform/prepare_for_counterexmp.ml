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
