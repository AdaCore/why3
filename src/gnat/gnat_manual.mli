open Why3

type goal = Session_itp.proofNodeID
type attempt = Session_itp.proofAttemptID

val manual_attempt_of_goal : Session_itp.session -> goal -> attempt option

val is_new_manual_proof : Session_itp.session -> goal -> bool

(* Returns the name of the created file which will then be used as file name for
   the manual prover *)
val create_prover_file :
  Controller_itp.controller -> goal -> Gnat_expl.check -> Whyconf.prover -> string

(* Get the file associated to the goal with the current manual prover.
   If the current prover is not manual None is returned *)
val manual_proof_info : Session_itp.session -> Session_itp.proofAttemptID -> (string * string) option
