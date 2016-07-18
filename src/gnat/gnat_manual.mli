open Why3

type goal = int Session.goal
type attempt = int Session.proof_attempt

val manual_attempt_of_goal : goal -> attempt option

val is_new_manual_proof : goal -> bool

(* Create a new file with the goal to be proved and
   adds an external proof. Returns the name of the created file *)
val create_prover_file :
  goal -> Gnat_expl.check -> Gnat_config.prover -> attempt

(* Get the file associated to the goal with the current manual prover.
   If the current prover is not manual None is returned *)
val manual_proof_info : attempt -> (string * string) option
