

open Format
open Why



let async = ref (fun f () -> f ())

type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)


(**** queues of events to process ****)

type attempt = bool * int * int * string * string * Driver.driver * 
    (proof_attempt_status -> float -> string -> unit) * Task.task 

(* queue of external proof attempts *)
let prover_attempts_queue : attempt Queue.t = Queue.create ()

(* queue of transformations *)
let transf_queue  : 
    ((Task.task list -> unit) * 'a Trans.trans * Task.task) Queue.t 
    = Queue.create ()

(* queue of prover answers *)
let answers_queue  : (attempt * proof_attempt_status * float * string) Queue.t 
    = Queue.create ()

(* number of running external proofs *)
let running_proofs = ref 0
let maximum_running_proofs = ref 2

(* they are protected by a lock *)
let queue_lock = Mutex.create ()
let queue_condition = Condition.create ()




(***** handler of events *****)

let event_handler () =
  Mutex.lock queue_lock;
  while 
    Queue.is_empty transf_queue && 
      Queue.is_empty answers_queue && 
      (Queue.is_empty prover_attempts_queue ||
         !running_proofs >= !maximum_running_proofs)
  do
    Condition.wait queue_condition queue_lock
  done;
  try
    let (a,res,time,output) = Queue.pop answers_queue in
    decr running_proofs;
    Mutex.unlock queue_lock;
(*
    eprintf "[Why thread] Scheduler.event_handler: got prover answer@.";
*)
    (* TODO: update database *)
    (* call GUI callback with argument [res] *)
    let (_,_,_,_,_,_,callback,_) = a in
    !async (fun () -> callback res time output) ()
  with Queue.Empty ->
    try
      let (callback,transf,task) = Queue.pop transf_queue in
      Mutex.unlock queue_lock;
      let subtasks : Task.task list = Trans.apply transf task in
      (* TODO: update database *)
      (* call GUI back given new subgoals *)
      !async (fun () -> callback subtasks) ()
    with Queue.Empty ->
      (* since answers_queue and transf_queue are empty, 
         we are sure that both
         prover_attempts_queue is non empty and
         running_proofs < maximum_running_proofs
      *)
      try
        let a = Queue.pop prover_attempts_queue in
        incr running_proofs;
        Mutex.unlock queue_lock;
        (* build the prover task from goal in [a] *)
        let (debug,timelimit,memlimit,_prover,command,driver,callback,goal) = a 
        in
        !async (fun () -> callback Running 0.0 "") ();
        try
          let call_prover : unit -> Call_provers.prover_result = 
            if false && debug then 
              Format.eprintf "Task for prover: %a@." 
                (Driver.print_task driver) goal;
            Driver.prove_task ~command ~timelimit ~memlimit driver goal
          in
          let (_ : Thread.t) = Thread.create 
            (fun () -> 
               let r = call_prover () in
               Mutex.lock queue_lock;
               let res =
                 match r.Call_provers.pr_answer with
                   | Call_provers.Valid -> Success         
                   | Call_provers.Timeout -> Timeout
                   | Call_provers.Invalid | Call_provers.Unknown _ -> Unknown
                   | Call_provers.Failure _ | Call_provers.HighFailure 
                       -> HighFailure
               in
               Queue.push (a,res,r.Call_provers.pr_time,r.Call_provers.pr_output) answers_queue ;
               Condition.signal queue_condition;
               Mutex.unlock queue_lock;
               ()
            )
            ()
          in ()
        with
          | e ->
            eprintf "%a@." Exn_printer.exn_printer e;
            Mutex.lock queue_lock;
            Queue.push (a,HighFailure,0.0,"Prover call failed") answers_queue ;
            (* Condition.signal queue_condition; *)
            Mutex.unlock queue_lock;
            ()
     with Queue.Empty -> 
        eprintf "Scheduler.event_handler: unexpected empty queues@.";
        assert false


(***** start of the scheduler thread ****)

let (_scheduler_thread : Thread.t) =
  Thread.create 
    (fun () ->
       try
         (* loop forever *)
         while true do
           event_handler ()
         done;
         assert false
       with
           e -> 
             eprintf "Scheduler thread stopped unexpectedly@.";
             raise e)
    ()


(***** to be called from GUI ****)

let schedule_proof_attempt ~debug ~timelimit ~memlimit ~prover 
    ~command ~driver ~callback
    goal =
  Mutex.lock queue_lock;
  Queue.push (debug,timelimit,memlimit,prover,command,driver,callback,goal)
    prover_attempts_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()

let apply_transformation ~callback transf goal =
  Mutex.lock queue_lock;
  Queue.push (callback,transf,goal) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()
  

