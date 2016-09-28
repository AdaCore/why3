open Why3

type key = int
(* The key type, with which we identify nodes in the Why3 VC tree *)

module Keygen : sig
   (* A small module that provides a trivial key generator for the session tree
    *)
   val keygen : ?parent:'a -> unit -> key
end

val init : unit -> unit
(* connect to proof server *)

val run_goal :
  cntexample : bool ->
  ?limit:Call_provers.resource_limit ->
  Session.loaded_prover ->
    int Session.goal -> unit
(* run a prover on a goal. This function returs immediately.
   @param cntexample indicates whether the prover should be queried for a
   counterexample. *)

val handle_proof_results :
   (key Session.proof_attempt -> Session.proof_attempt_status -> unit)
   -> unit
(* Wait for proof results. When proof results arrive, call the callback
   function on each result. The callback can call run_goal to spawn new
   provers. The function returns when no results are pending from the proof
   server. *)
