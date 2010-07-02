

let attempts = Queue.create ()

let running_proofs = ref 0
let maximum_running_proofs = ref 1

(*
let start_queue_thread n =
  if !maximum_running_proofs > 0 
  then failwith "Scheduler: queue thread already running";
  if n <= 0 then invalid_arg "Scheduler.start_queue_thread";
  maximum_running_proofs := n;
*)  


let try_prover ~debug:bool ~timelimit:int ~memlimit:int ~prover:prover 
    ~command:string ~driver:Why.Driver.driver ~callback:(unit -> unit) 
    goal =
  let call = 
    try
      Db.try_prover ~debug ~timelimit ~memlimit ~prover ~command ~driver goal 
    with Db.AlreadyAttempted ->
      raise Exit
  in
  (* store the attemp into the queue *)
  Queue.push (prepare_goal,callback) attempts;
  (* try to run attempt if resource available *)
  while !running_proofs < !maximum_running_proofs do
    incr running_proofs;
    call ();
    callback ();
    decr running_proofs;
  done
