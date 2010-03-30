

(** {1 Proof manager database} *)

(** {2 proof goals in a proof project} *)

type goal

type theory_lemma_identifier

type loc

type explain

type identifier

type origin =
  | Lemma of theory_lemma_identifier
  | VCfun of loc * explain * identifier
  | Subgoal of goal

val origin : goal -> origin

type proof_result = Valid | Timeout | Failed  

type prover_id

type proof_attempt =
  { proved_id : prover_id;
      (* prover identifier *)
    timelimit : int;
      (* CPU limit in seconds *)
    obsolete : bool;
      (* when true, goal as changed after that proof attempt *)
    result : proof_result;
    result_time : float ;
      (* CPU time for the prover run *)
    trace : string 
      (* any kind of trace for the prover. For an interactive prover, 
	 gives the file name for the current proof script *)
  } 

type tactic =
  | Attempt of proof_attempt
  | Split of goal * goal

val tactics : goal -> tactic list

val proved : goal -> bool
(** proved(g) == true iff
   exists tactic t in tactics(g), 
      (t = Attempt a and a.result == Valid and a.obsolete == false) or
      (t = Split(g1,g2)) and proved(g1) and proved(g2)
*)


(** {2 database for a proof project} *)

type proof_db

val get_goals : proof_db -> goal list

val get_subtask : proof_db -> string -> proof_db list

(** {2 add a proof attempt} *)


exception AlreadyAttempted

val try_prover : proof_db -> goal -> prover_id -> timelimit:int -> unit
(** (try_prover db g p t) attempts to prove goal g with prover p within time limit t

    if their already exist a proof attempt with the same prover and time limit, 
    and with a different time limit and a result different from Timeout, then raise
    AlreadyAttempted. Otherwise, runs the prover, and updates the database accordingly to its
    result. (do not return until the result is obtained ???) 

    Note: the invariant above is maintained, that is proved status are updated for any goal
    that depend on this result

*)

(** {2 Update goals in a project} *)

val goal_update: proof_db -> goal -> unit 
(** updates the database with the new goal. If a goal with the same origin already exists, it is checked
whether the formula to prove is different or not. If it is the same, proof attempts are preserved. If not the same,
former proof attempts are marked as obsolete. 
*)

val mark_all_as_obsolete : proof_db -> goal -> unit
(** mark all goals as obsolete *)

  



