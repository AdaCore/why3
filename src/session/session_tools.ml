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

open Whyconf
open Session

(** convert unknown prover *)
let unknown_to_known_provers provers pu =
  Mprover.fold (fun pk _ (others,name,version) ->
    match
      pk.prover_name = pu.prover_name,
      pk.prover_version = pu.prover_version,
      pk.prover_altern = pu.prover_altern with
        | false, _, _ -> pk::others, name, version
        | _, false, _ -> others, pk::name, version
        | _           -> others, name, pk::version
  ) provers ([],[],[])

let utkp provers pu () =
  let _,name,version = unknown_to_known_provers provers pu in
  version@name

let convert_unknown_prover ~keygen env_session =
  let known_provers = get_provers env_session.whyconf in
  let provers = get_used_provers env_session.session in
  let unknown_provers = Mprover.set_diff provers known_provers in
  if not (Sprover.is_empty unknown_provers) then begin
    (* construct the list of compatible provers for each unknown provers *)
    let unknown_provers =
      Mprover.mapi (utkp known_provers) unknown_provers in
    session_iter_proof_attempt (fun pr ->
      let pks = Mprover.find_def [] pr.proof_prover unknown_provers in
      List.iter (fun pk ->
        (* If such a prover already exists we add nothing *)
        if not (PHprover.mem (goal_external_proofs pr.proof_parent) pk) then
          ignore (copy_external_proof ~keygen ~prover:pk pr)
      ) pks;
    ) env_session.session
  end

(** filter the proof attempt *)
let filter_proof_attempt ?notify f s =
  session_iter_proof_attempt (fun pr ->
    if not (f pr) then remove_external_proof ?notify pr) s

(** get all proof_attempt *)
let all_proof_attempts s =
  let l = ref [] in
  session_iter_proof_attempt (fun pr -> l:=pr::!l) s;
  !l

(** apply a transformation on all the proof_attempt *)
let transform_proof_attempt ?notify ~keygen env_session tr_name =
  let replace pr =
    let g = pr.proof_parent in
    remove_external_proof ?notify pr;
    let tr =
      try
        PHstr.find (goal_transformations g) tr_name
      with Not_found ->
        add_registered_transformation ~keygen env_session tr_name g
    in
    let add_pa sg =
      if not (PHprover.mem (goal_external_proofs sg) pr.proof_prover) then
        ignore (copy_external_proof ~keygen ~goal:sg
                  ~attempt_status:Interrupted pr)
    in
    List.iter add_pa tr.transf_goals in
  let proofs = all_proof_attempts env_session.session in
  List.iter replace proofs
