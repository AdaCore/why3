

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

type theory_lemma_identifier

type loc

type explain

type identifier

type goal_origin =
  | Lemma of theory_lemma_identifier
  | VCfun of loc * explain * identifier
  | Subgoal of goal

and goal =
    {
      origin : goal_origin;
      attempts : attempt list;
      proved : bool;
      (** invariant: g.proved == true iff
             exists attempts a in g.attempts, 
      (a = External e and e.result == Valid and a.obsolete == false) or
      (a = Transf(gl) and forall g in gl, g.proved
      *)
      observers: (bool -> unit) list;
      (** observers that wants to be notified by any changes of the proved status *)
    }


(** {2 database for a proof project} *)

type proof_db

val get_goals : proof_db -> goal list

val get_subtask : proof_db -> string -> proof_db list

(** {2 attempts to solve goals} *)

exception AlreadyAttempted

val try_prover : goal -> Driver.driver -> timelimit:int -> proof_db -> unit
  (** attempts to prove goal with the given prover. This function adds
      a new corresponding attempt for that goal, sets its current
      status to Running, launches the prover in a separate process and
      returns immediately.

      Upon termination of the external process, the prover's answer is
      retrieved and database is updated. The [proved] field of the
      goal is updated, and also these of any goal affected, according
      to invariant above. Goal observers are notified of any change
      of goal statuses.

      @param timelimit CPU time limit given for that attempt

      @raise AlreadyAttempted if there already exists an external proof
      attempt with the same driver and time limit, or with a different
      time limit and a result different from Timeout


  *)

val add_transformation: goal -> transf -> proof_db -> unit
  (** adds a transformation on the goal. This function adds a new
      corresponding attempt for that goal, computes the subgoals and
      and them in the database. In the case where no subgoal is
      genereated, the [proved] field is updated, and those of parent
      goals.

      @raise AlreadyAttempted if this transformation has already been attempted

  *)


(** TODO: removal of attempts *)

(* {2 goal updates} *)

val add_or_replace_goal: proof_db -> goal -> unit 
  (** updates the database with the new goal.  If a goal with the same
      origin already exists, it is checked whether the task to
      prove is different or not. If it is the same, proof attempts are
      preserved. If not the same, former proof attempts are marked as
      obsolete.
  *)

(** TODO: full update, removing goals that are not pertinetn anymore *)


  



