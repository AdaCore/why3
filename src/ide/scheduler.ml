(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


open Format
open Why
open Worker

(** max scheduled proofs / max running proofs *)
let coef_buf = 1

let async = ref (fun f () -> f ())

let debug = Debug.register_flag "scheduler"

type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)

let print_pas fmt = function
  | Scheduled -> fprintf fmt "Scheduled"
  | Running -> fprintf fmt "Running"
  | InternalFailure exn ->
    fprintf fmt "InternalFailure %a" Exn_printer.exn_printer exn
  | Done pr -> Call_provers.print_prover_result fmt pr
(**** queues of events to process ****)

type callback = proof_attempt_status -> unit
type attempt = bool * int * int * in_channel option * string * Driver.driver *
    callback * Task.task

(* queue of external proof attempts *)
let prover_attempts_queue : attempt Queue.t = Queue.create ()

(* queue of proof editing tasks *)
let proof_edition_queue : (bool * string * string * Driver.driver *
    (unit -> unit) * Task.task)  Queue.t = Queue.create ()

type ('a,'b) doable = { callback : 'b -> unit;
                        argument : 'a;
                        funct    : 'a -> 'b   }

type exists_doable = { exists : 'a 'b. ('a,'b) doable -> unit }

type job =
  | TaskL of (Task.task list -> unit) * Task.task list Trans.trans * Task.task
  | Task of (Task.task -> unit) * Task.task Trans.trans * Task.task
  | Do of (exists_doable -> unit)

(* queue of transformations *)
let transf_queue  : job Queue.t = Queue.create ()

type answer =
  | Prover_answer of callback * (unit -> Call_provers.prover_result)
  | Editor_exited of (unit -> unit)
(* queue of prover answers *)
let answers_queue  : answer Queue.t = Queue.create ()

(* number of scheduled external proofs *)
let scheduled_proofs = ref 0
let maximum_running_proofs = ref 2

(* they are protected by a lock *)
let queue_lock = Mutex.create ()
let queue_condition = Condition.create ()

(* number of running external proofs *)
let running_proofs = ref 0

(* it is protected by a lock *)
let running_lock = Mutex.create ()
let running_condition = Condition.create ()

let print_debug_nb_running () =
  Debug.dprintf debug
    "scheduled_proofs = %i; running_proofs = %i;@."
    !scheduled_proofs !running_proofs

(***** handler of events *****)

(*** collect answers from provers or editors *)
let collect_answers () =
  match Queue.pop answers_queue with
    | Prover_answer (callback,r) ->
      Mutex.unlock queue_lock;
      let res = r () in
      (*
        eprintf
        "[Why thread] Scheduler.event_handler: got prover answer@.";
      *)
      (* call GUI callback with argument [res] *)
      !async (fun () -> callback (Done res)) ()
    | Editor_exited callback ->
      Mutex.unlock queue_lock;
      !async callback ()

(**** apply transformations *)
let apply_transform () =
  let k = Queue.pop transf_queue in
  Mutex.unlock queue_lock;
  Thread.yield ();
  match k with
    | TaskL (cb, tf, task) ->
      let subtasks : Task.task list = Trans.apply tf task in
      !async (fun () -> cb subtasks) ()
    | Task (cb,tf, task) ->
      let task = Trans.apply tf task in
      !async (fun () -> cb task) ()
    | Do e ->
      let f d =
        let r = d.funct d.argument in
        !async (fun () -> d.callback r) () in
      e {exists = f}

(**** edit proofs *)
let edit_proof () =
  let (_debug,editor,file,driver,callback,goal) =
    Queue.pop proof_edition_queue in
  Mutex.unlock queue_lock;
  let old =
    if Sys.file_exists file
    then
      begin
	let backup = file ^ ".bak" in
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

(* start new external proof attempt *)
(* since answers_queue and transf_queue are empty,
   we are sure that both
   prover_attempts_queue is non empty and
   scheduled_proofs < maximum_running_proofs * coef_buf
*)

let new_external_proof =
  let run_external (call_prover,callback) =
    Mutex.lock queue_lock;
    decr scheduled_proofs;
    incr running_proofs;
    print_debug_nb_running ();
    Condition.signal queue_condition;
    Mutex.unlock queue_lock;
    !async (fun () -> callback Running) ();
    let r = call_prover () in
    Mutex.lock queue_lock;
    decr running_proofs;
    print_debug_nb_running ();
    Queue.push (Prover_answer (callback,r)) answers_queue ;
    Condition.signal queue_condition;
    Mutex.unlock queue_lock in
  let external_workers =
    ManyWorkers.create maximum_running_proofs run_external in
  fun () ->
  if !scheduled_proofs >= !maximum_running_proofs * coef_buf
  then raise Queue.Empty;
  let (_debug,timelimit,memlimit,old,command,driver,callback,goal) =
    Queue.pop prover_attempts_queue
  in
  incr scheduled_proofs;
  print_debug_nb_running ();
  Debug.dprintf debug
    "%a is sent to driver;@."
    (fun fmt g -> Pretty.print_pr fmt (Task.task_goal g)) goal;
  Mutex.unlock queue_lock;
  Thread.yield ();
        (* build the prover task from goal in [a] *)
  try
    let call_prover : unit -> unit -> Call_provers.prover_result =
            (*
              if debug then
              Format.eprintf "Task for prover: %a@."
              (Driver.print_task driver) goal;
            *)
      Driver.prove_task ?old ~command ~timelimit ~memlimit driver goal
    in
    ManyWorkers.add_work external_workers (call_prover,callback);
  with
    | e ->
      eprintf "%a@." Exn_printer.exn_printer e;
      Mutex.lock queue_lock;
      decr scheduled_proofs;
      Mutex.unlock queue_lock;
      !async (fun () -> callback (InternalFailure e)) ()

type priority = (unit -> unit) list

let interactive : priority = [collect_answers;
                              apply_transform;
                              edit_proof;
                              new_external_proof]

let intensive : priority = [collect_answers;
                            new_external_proof;
                            apply_transform]

let priority = ref interactive

let set_priority = (:=) priority

let event_handler () =
  Mutex.lock queue_lock;
  while
    Queue.is_empty transf_queue &&
      Queue.is_empty answers_queue &&
      Queue.is_empty proof_edition_queue &&
      (Queue.is_empty prover_attempts_queue ||
         !scheduled_proofs >= !maximum_running_proofs * coef_buf)
  do
    Condition.wait queue_condition queue_lock
  done;
  let rec try_all = function
    | [] ->
      eprintf "Scheduler.event_handler: unexpected empty queues@.";
      assert false
    | f::l -> try f () with Queue.Empty -> try_all l in
  try_all !priority

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
             eprintf "Scheduler thread stopped unexpectedly : %a@."
             Exn_printer.exn_printer e;
             raise e)
    ()


(***** to be called from GUI ****)

let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback
    goal =
  !async (fun () -> callback Scheduled) ();
  Mutex.lock queue_lock;
  Queue.push (debug,timelimit,memlimit,old,command,driver,callback,goal)
    prover_attempts_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock

let create_proof_attempt  ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback
    goal =
  (debug,timelimit,memlimit,old,command,driver,callback,goal)

let transfer_proof_attempts q =
  Queue.iter (fun (_,_,_,_,_,_,callback,_) ->
    !async (fun () -> callback Scheduled) ()) q;
  Mutex.lock queue_lock;
  Queue.transfer q prover_attempts_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock

let schedule_some_proof_attempts ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback
    goal q =
  Queue.add
    (debug,timelimit,memlimit,old,command,driver,callback,goal) q;
  if Queue.length q >= !maximum_running_proofs * coef_buf * 2 then
    transfer_proof_attempts q


let edit_proof ~debug ~editor ~file ~driver ~callback goal =
  Mutex.lock queue_lock;
  Queue.push (debug,editor,file,driver,callback,goal) proof_edition_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock

let apply_transformation ~callback transf goal =
  Mutex.lock queue_lock;
  Queue.push (Task (callback,transf,goal)) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock


let apply_transformation_l ~callback transf goal =
  Mutex.lock queue_lock;
  Queue.push (TaskL (callback,transf,goal)) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock


let do_why ~callback funct argument =
  let doable = { callback = callback;
                 argument = argument;
                 funct    = funct } in
  let exists f = f.exists doable in
  Mutex.lock queue_lock;
  Queue.push (Do exists) transf_queue;
  Condition.signal queue_condition;
  Mutex.unlock queue_lock

(* TODO : understand Thread.Event *)
let do_why_sync funct argument =
  let m = Mutex.create () in
  let c = Condition.create () in
  let r = ref None in
  let cb res =
    Mutex.lock m; r := Some res; Condition.signal c; Mutex.unlock m in
  do_why ~callback:cb funct argument;
  Mutex.lock m; while !r = None do Condition.wait c m done;
  Util.of_option !r
