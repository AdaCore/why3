

open Format
open Why



let async = ref (fun f () -> f ())

type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)

(**** queues of events to process ****)

type callback = proof_attempt_status -> unit
type attempt = bool * int * int * in_channel option * string * Driver.driver *
    callback * Task.task

(* queue of external proof attempts *)
let prover_attempts_queue : attempt Queue.t = Queue.create ()

(* queue of proof editing tasks *)
let proof_edition_queue : (bool * string * string * Driver.driver *
    (unit -> unit) * Task.task)  Queue.t = Queue.create ()

type job =
  | TaskL of (Task.task list -> unit) * Task.task list Trans.trans * Task.task
  | Task of (Task.task -> unit) * Task.task Trans.trans * Task.task

(* queue of transformations *)
let transf_queue  : job Queue.t = Queue.create ()

type answer =
  | Prover_answer of callback * proof_attempt_status
  | Editor_exited of (unit -> unit)
(* queue of prover answers *)
let answers_queue  : answer Queue.t = Queue.create ()

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
      Queue.is_empty proof_edition_queue &&
      (Queue.is_empty prover_attempts_queue ||
         !running_proofs >= !maximum_running_proofs)
  do
    Condition.wait queue_condition queue_lock
  done;
  try begin
    (* priority 1: collect answers from provers or editors *)
    match Queue.pop answers_queue with
      | Prover_answer (callback,res) ->
          decr running_proofs;
          Mutex.unlock queue_lock;
          (*
            eprintf
            "[Why thread] Scheduler.event_handler: got prover answer@.";
          *)
          (* call GUI callback with argument [res] *)
          !async (fun () -> callback res) ()
      | Editor_exited callback ->
          Mutex.unlock queue_lock;
          !async callback ()
  end
  with Queue.Empty ->
    try
      (* priority 2: apply transformations *)
      let k = Queue.pop transf_queue in
      Mutex.unlock queue_lock;
      match k with
      | TaskL (cb, tf, task) ->
          let subtasks : Task.task list = Trans.apply tf task in
          !async (fun () -> cb subtasks) ()
      | Task (cb,tf, task) ->
          let task = Trans.apply tf task in
          !async (fun () -> cb task) ()
    with Queue.Empty ->
    try
      (* priority 3: edit proofs *)
      let (_debug,editor,file,driver,callback,goal) =
        Queue.pop proof_edition_queue in
      Mutex.unlock queue_lock;
      let backup = file ^ ".bak" in
      let old =
        if Sys.file_exists file
        then
          begin
            Sys.rename file backup;
            Some(open_in backup)
          end
        else None
      in
      let ch = open_out file in
      let fmt = formatter_of_out_channel ch in
      Driver.print_task ?old driver fmt goal;
      Util.option_iter close_in old;
      close_out ch;
      let (_ : Thread.t) = Thread.create
        (fun () ->
           let _ = Sys.command(editor ^ " " ^ file) in
           Mutex.lock queue_lock;
           Queue.push (Editor_exited callback) answers_queue ;
           Condition.signal queue_condition;
           Mutex.unlock queue_lock)
        ()
      in ()
    with Queue.Empty ->
      (* priority low: start new external proof attempt *)
      (* since answers_queue and transf_queue are empty,
         we are sure that both
         prover_attempts_queue is non empty and
         running_proofs < maximum_running_proofs
      *)
      try
        let (_debug,timelimit,memlimit,old,command,driver,callback,goal) =
          Queue.pop prover_attempts_queue
        in
        incr running_proofs;
        Mutex.unlock queue_lock;
        (* build the prover task from goal in [a] *)
        !async (fun () -> callback Running) ();
        try
          let call_prover : unit -> Call_provers.prover_result =
(*
            if debug then
              Format.eprintf "Task for prover: %a@."
                (Driver.print_task driver) goal;
*)
            Driver.prove_task ?old ~command ~timelimit ~memlimit driver goal
          in
          let (_ : Thread.t) = Thread.create
            (fun () ->
               let r = call_prover () in
               Mutex.lock queue_lock;
               let res = Done r in
               Queue.push
                 (Prover_answer (callback,res)) answers_queue ;
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
            Queue.push
              (Prover_answer (callback, InternalFailure e)) answers_queue ;
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

let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback
    goal =
  Mutex.lock queue_lock;
  Queue.push (debug,timelimit,memlimit,old,command,driver,callback,goal)
    prover_attempts_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()

let edit_proof ~debug ~editor ~file ~driver ~callback goal =
  Mutex.lock queue_lock;
  Queue.push (debug,editor,file,driver,callback,goal) proof_edition_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()

let apply_transformation ~callback transf goal =
  Mutex.lock queue_lock;
  Queue.push (Task (callback,transf,goal)) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()


let apply_transformation_l ~callback transf goal =
  Mutex.lock queue_lock;
  Queue.push (TaskL (callback,transf,goal)) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock;
  ()
