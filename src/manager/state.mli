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


(** {1 Proof manager database} *)


(** {2 proof attempts and transformations} *)

(** status of an external proof attempt *)
type proof_attempt_status =
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)

(** a proof attempt by some external provers *)
type external_proof =
  { prover : Driver.driver; (** prover driver *)
    timelimit : int; (** CPU limit given in seconds *)
    status : proof_attempt_status; (** the current state *)
    result_time : float ; (** CPU time for that run *)
    trace : string;
      (** any kind of trace returned by the prover.
          when redoing the same attempt, the former trace is sent again *)
    obsolete : bool;
      (** when true, goal as changed after that proof attempt *)
  }

type transf = Task.task Register.tlist_reg

(** an proof attempt is either an external proof or a transformation
    into subtasks *)
type attempt =
  | External of external_proof
  | Transf of transf

(** {2 proof goals in a proof project} *)


type loc

type explain

type identifier

type goal_origin =
  | Goal of Decl.prsymbol
  | VCfun of loc * explain * identifier
  | Subgoal of goal

and goal =
    {
      task : Task.task;
      task_checksum: string;
      origin : goal_origin;
      mutable attempts : attempt list;
      mutable proved : bool;
      (** invariant: g.proved == true iff
             exists attempts a in g.attempts, a.obsolete == false and
             (a = External e and e.result == Valid or
              a = Transf(gl) and forall g in gl, g.proved)
      *)
      mutable observers: (bool -> unit) list;
      (** observers that wants to be notified by any changes of the proved status *)
    }


(** {2 database for a proof project} *)

type loc_record_in_db =
  { file : string;
    line : int;
    cbegin : int;
    cend : int;
  }

type goal_record_in_db =
  {
    task_checksum : string;
    parent : transf_in_db option;
    name : string; (* qualified proposition name *)
    origin : loc_record_in_db option;
    external_proofs : external_proof_in_db list;
    transformations : transf_in_db list;
    proved : bool;
  }

and external_proof_in_db =
  {
    prover : string; (** prover identifier *)
    timelimit : int; (** CPU limit given in seconds *)
    memlimit : int; (** VM limit given in megabytes *)
    status : int; (** enum{proof_attempt_status}; the current state *)
    result_time : float ; (** CPU time for that run in seconds *)
    trace : string option;
      (** any kind of trace returned by an automatic prover,
          or any kind of proof script for an interactive prover *)
    obsolete : bool;
  }

and transf_in_db =
  {
    name : string; (** transformation name *)
    obsolete : bool;
  }

val read_db_from_file : unit -> goal list
(** returns the set of root goals *)

(** {2 attempts to solve goals} *)

exception AlreadyAttempted

val try_prover :
  timelimit:int -> ?memlimit:int -> goal -> Driver.driver -> unit
  (** attempts to prove goal with the given prover. This function adds
      a new corresponding attempt for that goal, sets its current
      status to Running, launches the prover in a separate process and
      returns immediately.

      Upon termination of the external process, the prover's answer is
      retrieved and database is updated. The [proved] field of the
      database is updated, and also these of any goal affected, according
      to invariant above. Goal observers are notified of any change
      of goal statuses.

      @param timelimit CPU time limit given for that attempt, must be positive

      @raise AlreadyAttempted if there already exists a non-obsolete
      external proof attempt with the same driver and time limit, or
      with a different time limit and a result different from Timeout


  *)

val add_transformation: goal -> transf -> unit
  (** adds a transformation on the goal. This function adds a new
      corresponding attempt for that goal, computes the subgoals and
      and them in the database. In the case where no subgoal is
      genereated, the [proved] field is updated, and those of parent
      goals.

      if this transformation has already been attempted but is markes
      as obsolete, it is retried, and the new lists of goals is
      carefully matched with the older subgoals, so that if some
      subgoals are identical to older ones, then the proof is kept.
      Notice that no old proof attempts should be lost in this
      process, e.g if the old trans formation produced 3 subgoals
      A,B,C, C was proved interactively, and the new transformations
      produces only 2 goals, the interactive proof of C is keep in an
      extra dummy goal "true"

      @raise AlreadyAttempted if this transformation has already been attempted
      and is not obsolete

  *)



(** TODO: removal of attempts *)

(* {2 goal updates} *)

val add_or_replace_goal: goal -> unit
  (** updates the database with the new goal.  If a goal with the same
      origin already exists, it is checked whether the task to
      prove is different or not. If it is the same, proof attempts are
      preserved. If not the same, former proof attempts are marked as
      obsolete.


      IMPORTANT: this kills every running prover tasks

  *)

(** TODO: full update, removing goals that are not pertinent anymore *)






