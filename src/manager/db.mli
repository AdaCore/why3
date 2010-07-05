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

(** {1 Proof manager database} *)

(** {2 Current proof state} *)

(** prover data *)

type prover 
  (** abstract type for the set of provers of the database *)

val prover_name : prover -> string
  (** name of a prover *)

val get_prover : string -> prover
  (** retrieves prover from its unique name.  creates a new prover if
      needed. *)

(** status of an external proof attempt *)
type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)

val print_status : Format.formatter -> proof_attempt_status -> unit

type external_proof
  (** abstract type for a proof attempt with an external prover *)

val prover : external_proof -> prover
  (** the prover used for this attempt *)

val timelimit : external_proof -> int
  (** the time limit chosen for this attempt *)

val memlimit : external_proof -> int
  (** the memory limit chosen for this attempt *)

val status : external_proof -> proof_attempt_status
  (** the current status for this attempt *)

val result_time : external_proof -> float
  (** the time taken for this attempt. Only meaningfull for attempts
      that are not Scheduled or Running. *)

val trace : external_proof -> string
  (** a trace of execution of this attempt. Not used yet. *)

val proof_obsolete : external_proof -> bool
  (** this attempt became obsolete because goal has changed. *)

type goal
  (** abstract type for goals *)

(** module Goal to allow use of goals in Hashtables or Map or Set *)
module Goal : sig
  
  type t = goal
      
  val hash : t -> int

  val equal : t -> t -> bool

  val compare : t -> t -> int

end

type transf_data =
    { transf_name : string;
      transf_action : Task.task Register.tlist_reg
    }

type transf

(** goal accessors *)


val goal_name : goal -> string
  (** returns a goal's name, if any *)
(*
  val parent : goal -> transf option
*)

(*
val goal_task : goal -> Task.task
*)
val goal_task_checksum: goal -> string
val external_proofs : goal -> external_proof list
  (** returns the set of external proof attempt for that goal *)

val transformations : goal -> transf list

val goal_proved : goal -> bool
  (** tells if the goal is proved valid or not.
      It returns true iff either
      {ul {li exists proof p in [external_proofs g] s.t.
          proof_obsolete p == false and status p = Valid}}
      or
      {ul {li exists transf t in [transformations g] s.t.
            transf_obsolete t == false and
            forall g in [subgoals t], [goal_proved g]}}
  *)



(** transf accessors *)

val transf_data : transf -> transf_data
val transf_obsolete :  transf -> bool
val subgoals : transf -> goal list



(** {2 The persistent database} *)

val init_base : string -> unit
(** opens or creates the current database, from given file name *)

val root_goals : unit -> goal list
(** returns the current set of root goals *)




(** {2 attempts to solve goals} *)

exception AlreadyAttempted

val try_prover : 
  debug:bool -> timelimit:int -> memlimit:int -> prover:prover -> 
  command:string -> driver:Driver.driver -> goal -> (unit -> unit)
  (** attempts to prove goal with the given prover.  This function
      prepares the goal for that prover, adds it as an new
      external_proof attempt, setting its current status to Scheduled,
      and returns immmediately a function.  When called, this function
      actually sets the status to running, launches the prover, and
      waits for its termination. Upon termination of the external
      process, the prover's answer is retrieved and database is
      updated. The [proved] field of the database is updated, and also
      these of any goal affected, according to invariant above.

      Although goal preparation is not re-entrant, the function
      returned initially is re-entrant, thus is suitable for being executed
      in a thread, in contexts where background execution of provers is wanted.
      
      @param timelimit CPU time limit given for that attempt, in
      seconds, must be positive. (unlimited attempts are not allowed
      with this function)

      @param memlimit memory limit given for that attempt, must be
      positive. If not given, does not limit memory consumption

      @raise AlreadyAttempted if there already exists a non-obsolete
      external proof attempt with the same prover and time limit, or
      with a lower or equal time limit and a result different from Timeout


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

val add_or_replace_task: tname:string -> name:string -> Task.task -> goal
  (** updates the database with the new goal called [name] in the
      theory called [tname]. If a goal with the same [(tname,name)]
      already exists, it is checked whether the task to prove is
      different or not. If it is the same, proof attempts are
      preserved. If not the same, former proof attempts are marked as
      obsolete.

      WARNING: the current implementation always adds a new task,
      without checking if it already exists

      IMPORTANT: this kills every running prover tasks

      
  *)

(** TODO: full update, removing goals that are not pertinent anymore *)


  
