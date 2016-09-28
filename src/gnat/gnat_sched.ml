open Why3

type key = int
module Keygen = struct

   let count = ref 0

   let keygen ?parent () =
      ignore (parent);
      incr count;
      !count
end

 type queue_entry =
   { goal   : int Session.goal;
     prover : Session.loaded_prover;
     cntexample : bool;
   }

module Intmap =
  Exthtbl.Make
  (struct
    type t = int
    let hash = Hashtbl.hash let equal =
    Pervasives.(=)
   end)

type running_goals =
  { mutable num : int;
    map : queue_entry Intmap.t
  }

let state = { num = 0; map = Intmap.create 17 }

let run_goal ~cntexample prover g =
  (* spawn a prover and return immediately. The return value is a tuple of type
     Call_provers.prover_call * Session.goal *)
  let base_prover = prover.Session.prover_config in
  let driver = prover.Session.prover_driver in
  let old, inplace, limit =
    match (base_prover.Whyconf.interactive,
           Session.PHprover.find_opt g.Session.goal_external_proofs
                                     base_prover.Whyconf.prover) with
    | true, Some { Session.proof_edited_as = Some fn } ->
       Some fn, true, Call_provers.empty_limit
    | _ ->
        let prover = base_prover.Whyconf.prover.Whyconf.prover_name in
        None, false, Gnat_config.limit ~prover in
  let id =
    Driver.prove_task
      ~command:(Whyconf.get_complete_command base_prover
      ~with_steps:(limit.Call_provers.limit_steps <>
                   Call_provers.empty_limit.Call_provers.limit_steps))
      ~cntexample ~limit ?old ~inplace driver (Session.goal_task g) in
  let entry = { goal = g; prover = prover; cntexample = cntexample } in
  state.num <- state.num + 1;
  Intmap.add state.map id entry

let handle_finished_call callback entry res =
  (* On a pair of the type post_prover_call * goal, register the proof result
     in the session and call the callback *)
  let g = entry.goal in
  let prover = entry.prover.Session.prover_config.Whyconf.prover in
  let res =
    (* we do not want to store succesful counter example proofs in the session,
       so we mark them unknown *)
    if entry.cntexample && res.Call_provers.pr_answer = Call_provers.Valid then
      { res with
        Call_provers.pr_answer =
          Call_provers.Unknown ("counter_example", Some Call_provers.Other)
      }
    else res in
  let pas = Session.Done res in
  let edit =
    match Session.PHprover.find_opt g.Session.goal_external_proofs prover with
    | Some pa -> pa.Session.proof_edited_as
    | _ -> None in
  let pa =
       Session.add_external_proof
         ~keygen:Keygen.keygen
         ~obsolete:false
         ~archived:false
	 ~limit:(Gnat_config.limit ~prover:prover.Whyconf.prover_name)
         ~edit
         g
         prover
         pas in
  callback pa pas

let finished_goal callback id res =
  let entry = Intmap.find state.map id in
  state.num <- state.num - 1;
  Intmap.remove state.map id;
  handle_finished_call callback entry res

let init () =
  if Gnat_config.stand_alone then begin
    Prove_client.connect_internal ();
    Unix.sleep 1
  end else
  Prove_client.connect_external Gnat_config.socket_name

let shut_down_proof_server () =
  Prove_client.disconnect ()

let handle_proof_results callback =
  let handle_list = List.iter (fun (id, res) ->
    match res with
    | None -> ()
    | Some r -> finished_goal callback id r)
  in
  while state.num > 0 do
    let l = Call_provers.wait_for_server_result ~blocking:true in
    handle_list l;
  done;
  shut_down_proof_server ()
