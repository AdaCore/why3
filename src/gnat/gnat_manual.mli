open Why3

type goal = int Session.goal

val is_new_manual_proof : goal -> bool

(* Create a new file with the goal to be proved and
   adds an external proof. Returns the name of the created file *)
val create_prover_file : goal -> string

(* Get the file associated to the goal with the current manual prover.
   If the current prover is not manual None is returned *)
val get_prover_file : goal -> string option
