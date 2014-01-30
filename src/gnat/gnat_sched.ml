open Why3

type key = int
module Keygen = struct

   let count = ref 0

   let keygen ?parent () =
      ignore (parent);
      incr count;
      !count
end

let goal_queue : int Session.goal Queue.t =
  (* the queue which contains the goals to be proved *)
  Queue.create ()

let add_goal g =
  (* simple wrapper for Queue.add *)
  Queue.add g goal_queue

let run_goal g =
  (* spawn a prover and return immediately. The return value is a tuple of type
     Call_provers.prover_call * Session.goal *)
  Driver.prove_task
    ~command:Gnat_config.prover.Whyconf.command
    ~timelimit:Gnat_config.timeout
    ~memlimit:0
    Gnat_config.prover_driver
    (Session.goal_task g) (),
  g

let rec take acc n =
  (* take up to n goals from the queue (less if the queue has less elements)
     and spawn them. Put the resulting pair (prover_call * goal) in the
     accumulator. *)
  if n <= 0 || Queue.is_empty goal_queue then acc
  else take (run_goal (Queue.pop goal_queue) :: acc) (n-1)

let filter_finished_goals =
  (* Given a list of pairs (prover_call * goal), return a pair of lists
       finished : (post_prover_call, goal)
       rest     : (prover_call, goal)
    where the first list contains all finished goals, and the second list all
    still unfinished ones. *)
  let rec filter fin unf l =
    match l with
    | [] -> fin, unf
    | ((p, g) as rp) :: rest ->
        begin match Call_provers.query_call p with
        | None -> filter fin (rp::unf) rest
        | Some post -> filter ((post, g) :: fin) unf rest
        end
  in
  filter [] []

let handle_finished_call callback (post, g) =
  (* On a pair of the type post_prover_call * goal, register the proof result
     in the session and call the callback *)
  let res = post () in
  let pas = (Session.Done res) in
  let pa =
    Session.add_external_proof
      ~keygen:Keygen.keygen
      ~obsolete:false
      ~archived:false
      ~timelimit:Gnat_config.timeout
      ~memlimit:0
      ~edit:None
      g
      Gnat_config.prover.Whyconf.prover
      pas in
  callback pa pas

let run callback =
  let l = take [] Gnat_config.parallel in
  let handle = handle_finished_call callback in
  let rec run l =
    (* l contains the currently running jobs. We first check if any are
       finished. *)
    let finished, rest = filter_finished_goals l in
    match finished = [], rest = [], Queue.is_empty goal_queue with
    | true, true, true ->
        (* everything is empty, stop *)
        ()
    | true, true, false ->
        (* nothing is running, but the queue is not empty, grab more *)
        let l = take [] Gnat_config.parallel in
        run l
    | true, false, _ ->
        (* nothing is finished, wait a bit more and try again *)
        ignore (Unix.select [] [] [] 0.1);
        run l
    | false, _, _ ->
        (* some provers have terminated. We replace them by new processes (do
           this first to maximize running processes) and handle the proof
           results *)
      let l = take rest (List.length finished) in
      List.iter handle finished;
      run l
  in
  run l


