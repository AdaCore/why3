(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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


open Why

val async: ((unit->unit)->unit->unit) ref
(** async f () should call [f ()] asynchronously, in a suitable way
    for the current user interface (e.g. GtkThread.async) *)

val maximum_running_proofs: int ref
(** bound on the number of prover processes running in parallel. 
    default is 2 *)

type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)

val schedule_proof_attempt : 
  debug:bool -> timelimit:int -> memlimit:int -> 
  prover:string (*Db.prover*) -> 
  command:string -> driver:Driver.driver -> 
  callback:(proof_attempt_status -> float -> unit) -> 
  Task.task (* Db.goal *) -> unit
  (** schedules an attempt to prove goal with the given prover.  This
      function just prepares the goal for the proof attempt, and puts
      it in the queue of waiting proof attempts, associated with its
      callback.

      The callback is called each time the status of that proves
      changes, typically from Scheduled, then Running, then Success or
      Timeout or Failure.
      
      @param timelimit CPU time limit given for that attempt, in
      seconds, must be positive. (unlimited attempts are not allowed
      with this function)

      @param memlimit memory limit given for that attempt, must be
      positive. If not given, does not limit memory consumption

      @raise AlreadyAttempted if there already exists a non-obsolete
      external proof attempt with the same prover and time limit, or
      with a lower or equal time limit and a result different from Timeout


  *)




(*
Local Variables: 
compile-command: "make -C ../.. bin/gwhy.byte"
End: 
*)




