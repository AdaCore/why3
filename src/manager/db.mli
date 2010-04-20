

(** {1 Proof manager database} *)

(*
type handle
  (** Database handle which can be used to create and retrieve objects *)

type transaction_mode = | Deferred | Immediate | Exclusive

val create :
  ?busyfn:(Sqlite3.db -> unit) -> ?mode:transaction_mode ->
  string -> handle
  (** [create db_name] opens a Sqlite3 database with filename
      [db_name] and create any tables if they are missing. 
      @return a
      database handle which can be used to create and retrieve objects in
      the database.  @raise Sql_error if a database error is
      encountered *)

(*
val raw: handle -> Sqlite3.db
  (** [raw db] @return the underlying Sqlite3 database for the
      connection, for advanced queries.  *)
*)
*)





(* {2 proof attempts and transformations} *)


(** {2 Current proof state} *)


(*
type db_ident (* = int64 *)
(** hidden type for record unique identifiers *)
*)

(*
type loc_record 
*)
(*= private
    { mutable id : db_ident option;
      (** when None, the record has never been stored in database yet *)
      mutable file : string;
      mutable line : int;
      mutable start : int;
      mutable stop : int;
    }
*)

(** status of an external proof attempt *)
type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | HighFailure (** external prover call failed *)

type prover_data =
    { prover_name : string;
      driver : Why.Driver.driver;
    }

type external_proof

val prover : external_proof -> prover_data
val timelimit : external_proof -> int
val memlimit : external_proof -> int
val status : external_proof -> proof_attempt_status
val result_time : external_proof -> float
val trace : external_proof -> string
val proof_obsolete : external_proof -> bool

(*
type goal_origin =
  | Goal of Decl.prsymbol
(*
  | VCfun of loc * explain * ...
  | Subgoal of goal
*)
*)

type goal

val goal_proved : goal -> bool
val goal_name : goal -> string

module Goal : sig
  
  type t = goal
      
  val hash : t -> int

  val equal : t -> t -> bool

  val compare : t -> t -> int

end

type transf_data =
    { transf_name : string;
      transf_action : Why.Task.task Why.Register.tlist_reg
    }

type transf

(** goal accessors *)

val goal_task : goal -> Why.Task.task
val goal_task_checksum: goal -> string
(*
  val parent : goal -> transf option
*)
val external_proofs : goal -> external_proof list
val transformations : goal -> transf list

val goal_proved : goal -> bool
  (** [goal_proved g] returns true iff either
      exists proof p in [external_proofs g] s.t.
          proof_obsolete p == false and status p = Valid
      or
      exists transf t in [transformations g] s.t.
            transf_obsolete t == false and
            forall g in [subgoals t], [goal_proved g]
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
  timelimit:int -> ?memlimit:int -> goal -> prover_data -> (unit -> unit)
  (** attempts to prove goal with the given prover.  This function
      prepares the goal for that prover, adds it as an new
      external_proof attempt, setting its current status to Running,
      and returns immmediately a function.  When called, this function
      actually launches the prover, and waits for its
      termination. Upon termination of the external process, the
      prover's answer is retrieved and database is updated. The
      [proved] field of the database is updated, and also these of any
      goal affected, according to invariant above. 

      Although goal preparation is not re-entrant, the function
      returned initially is re-entrant, thus is suitable for being executed
      in a thread, in contexts where background execution of provers is wanted.
      
      @param timelimit CPU time limit given for that attempt, in
      seconds, must be positive. (unlimited attempts are not allowed
      with this function)

      @param memlimit memory limit given for that attempt, must be
      positive. If not given, does not limit memory consumption

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

val add_or_replace_task: Why.Decl.prsymbol -> Why.Task.task -> goal
  (** updates the database with the new goal.  If a goal with the same
      origin already exists, it is checked whether the task to
      prove is different or not. If it is the same, proof attempts are
      preserved. If not the same, former proof attempts are marked as
      obsolete.

      WARNING: the current implementation always adds a new task, without checling if it already exists

      IMPORTANT: this kills every running prover tasks

      
  *)

(** TODO: full update, removing goals that are not pertinent anymore *)


  
