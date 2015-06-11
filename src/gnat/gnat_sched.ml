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
     prover : Gnat_config.prover
   }

let goal_queue : queue_entry Queue.t =
  (* the queue which contains the goals to be proved *)
  Queue.create ()

let add_goal prover g =
  (* simple wrapper for Queue.add *)
  Queue.add { goal = g; prover = prover } goal_queue

let run_goal entry =
  (* spawn a prover and return immediately. The return value is a tuple of type
     Call_provers.prover_call * Session.goal *)
  let g = entry.goal in
  let prover = entry.prover in
  let base_prover = prover.Gnat_config.prover in
  let driver = prover.Gnat_config.driver in
  let old, inplace, timeout =
    match (base_prover.Whyconf.interactive,
           Session.PHprover.find_opt g.Session.goal_external_proofs
                                     base_prover.Whyconf.prover) with
    | true, Some { Session.proof_edited_as = Some fn } ->
       Some fn, Some true, 0
    | _ -> None, None, Gnat_config.timeout in
  Driver.prove_task_server
    base_prover.Whyconf.command
    ~timelimit:timeout
    ~memlimit:0
    ~steplimit:Gnat_config.steps
    ?old:old ?inplace:inplace
    driver
    (Session.goal_task g)

module Intmap =
  Extmap.Make (struct type t = int let compare = Pervasives.compare end)

type running_goals =
  { num : int;
    map : queue_entry Intmap.t
  }

let empty = { num = 0; map = Intmap.empty }

let rec run_goals rg =
  if rg.num >= Gnat_config.parallel || Queue.is_empty goal_queue then rg
  else begin
    let entry = Queue.pop goal_queue in
    let id = run_goal entry in
    let rg =
      { num = rg.num + 1;
        map = Intmap.add id entry rg.map
      }
    in
    run_goals rg
  end

let handle_finished_call callback entry res =
  (* On a pair of the type post_prover_call * goal, register the proof result
     in the session and call the callback *)
  let g = entry.goal in
  let prover = entry.prover.Gnat_config.prover.Whyconf.prover in
  let pas = (Session.Done res) in
  let edit =
    match Session.PHprover.find_opt g.Session.goal_external_proofs prover with
    | Some pa -> pa.Session.proof_edited_as
    | _ -> None in
  let pa =
       Session.add_external_proof
         ~keygen:Keygen.keygen
         ~obsolete:false
         ~archived:false
         ~timelimit:Gnat_config.timeout
         ~memlimit:0
         ~edit
         g
         prover
         pas in
  callback pa pas

let finished_goal callback rg id res =
  let entry = Intmap.find id rg.map in
  let rg = { num = rg.num - 1; map = Intmap.remove id rg.map } in
  handle_finished_call callback entry res;
  rg

let server_pid = ref 0


let init_proof_server () =
  if Gnat_config.stand_alone then begin
    let bin_dir = Filename.dirname Sys.executable_name in
    let why3server = Filename.concat bin_dir "why3server" in
    server_pid :=
      Unix.create_process why3server
        [|"why3server"; "--socket"; Gnat_config.socket_name|]
        Unix.stdin Unix.stdout Unix.stderr;
    (* need to wait a bit before connecting. This is debug code, so not an
       issue to wait a second *)
    Unix.sleep 1
  end;
  Prove_client.connect ()

let shut_down_proof_server () =
    Prove_client.disconnect ();
    if Gnat_config.stand_alone then
      Unix.kill !server_pid 9

let run callback =
  if not (Queue.is_empty goal_queue) then begin
    init_proof_server ();
    let handle_list =
      List.fold_left (fun acc (id, res) -> finished_goal callback acc id res)
    in
    let rec run running_goals =
      let running_goals = run_goals running_goals in
      if running_goals.num > 0 then
        let l = Call_provers.wait_for_server_result () in
        run (handle_list running_goals l)
      else if Queue.is_empty goal_queue then ()
      else run running_goals
    in
    run empty;
    shut_down_proof_server ()
  end
