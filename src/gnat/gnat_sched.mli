open Why3

type key = int
(* The key type, with which we identify nodes in the Why3 VC tree *)

module Keygen : sig
   (* A small module that provides a trivial key generator for the session tree
    *)
   val keygen : ?parent:'a -> unit -> key
end

val add_goal : int Session.goal -> unit
(* add a goal to the Goal queue. This function returs immediately. *)

val run :
   (key Session.proof_attempt -> Session.proof_attempt_status -> unit)
   -> unit
(* Run the prover on all goals in the queue (and remove the goals from the
   queue). For each proof result, call the callback.  It is safe to call
   [add_goal] in the callback to add more goals. This function stops when all
   provers have finished and the queue is empty. *)
