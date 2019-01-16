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

open Task

let debug = Debug.register_info_flag "prepare_for_counterexmp"
  ~desc:"Print@ debugging@ messages@ about@ preparing@ the@ task@ \
    for@ getting@ counter-example."

let meta_get_counterexmp =
  Theory.register_meta_excl "get_counterexmp" [Theory.MTstring]
  ~desc:"Set@ when@ counter-example@ should@ be@ get."

let get_counterexmp task =
  let ce_meta = Task.find_meta_tds task meta_get_counterexmp in
  not (Theory.Stdecl.is_empty ce_meta.tds_set)

let meta_counterexmp_prover =
  Theory.register_meta_excl "counterexmp_prover" [Theory.MTstring]
  ~desc:"Contain@ name@ of@ prover@ for@ counterexamples."

let get_ce_prover task =
  let meta = Task.find_meta_tds task meta_counterexmp_prover in
  try (
    match (Theory.Stdecl.choose meta.tds_set).Theory.td_node with
    | Theory.Meta (_, [Theory.MAstr s]) -> s
    | _ -> "cvc4_ce"
   )
  with Not_found -> "cvc4_ce"

let prepare_for_counterexmp2 env task =
  if not (get_counterexmp task) then begin
    (* Counter-example will not be queried, do nothing *)
    Debug.dprintf debug "Not get ce@.";
    task
  end
  else begin
    (* Counter-example will be queried, prepare the task *)
    Debug.dprintf debug "Get ce@.";
    let comp_trans = Trans.seq [
      Introduction.simplify_intros;
      Intro_vc_vars_counterexmp.intro_vc_vars_counterexmp;
      Intro_projections_counterexmp.intro_projections_counterexmp env
    ] in
    Trans.apply comp_trans task
  end

let prepare_for_counterexmp env = Trans.store (prepare_for_counterexmp2 env)

let () = Trans.register_env_transform "prepare_for_counterexmp"
  prepare_for_counterexmp
  ~desc:"Transformation@ that@ prepares@ the@ task@ for@ querying@ for@ \
    the@ counter-example@ model.@ This@ transformation@ does@ so@ only@ \
    when@ the@ solver@ will@ be@ asked@ for@ the@ counter-example."
