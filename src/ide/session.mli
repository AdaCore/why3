(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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


open Why3

module type OBSERVER = sig
  type key
  val create: ?parent:key -> unit -> key
  val notify: key -> unit
  val remove: key -> unit
end

module Make(O: OBSERVER) : sig

(*****************************)
(*                           *)
(* static state of a session *)
(*                           *)
(*****************************)

  type proof_attempt_status =
    | Undone
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

  type proof_attempt = private
      { prover : prover_data;
        proof_goal : goal;
        proof_key : O.key;
        mutable proof_state : proof_attempt_status;
        mutable proof_obsolete : bool;
        mutable edited_as : string;
      }

  and goal_parent =
    | Theory of theory
    | Transf of transf

  and goal = private
      { goal_name : string;
	parent : goal_parent;
        task: Task.task;
        goal_key : O.key;
        mutable proved : bool;
        external_proofs: (string, proof_attempt) Hashtbl.t;
        transformations : (string, transf) Hashtbl.t;
      }

  and transf = private
      { parent_goal : goal;
	mutable transf_proved : bool;
        transf_key : O.key;
        mutable subgoals : goal list;
      }

  and theory = private
      { theory : Theory.theory;
        theory_key : O.key;
        theory_parent : file;
        mutable goals : goal list;
        mutable verified : bool;
      }

  and file = private
      { file_name : string;
        file_key : O.key;
        mutable theories: theory list;
        mutable file_verified : bool;
      }

  type any =
    | File of file
    | Theory of theory
    | Goal of goal
    | Proof_attempt of proof_attempt
    | Transformation of transf


  (*****************************)
  (*                           *)
  (*      save/load state      *)
  (*                           *)
  (*****************************)

  val open_session : string -> unit
    (** starts a new proof session, using directory given as argument 
        this reloads the previous session if any.

        Opening a session must be done prior to any other actions.
        And it cannot be done twice.

        TODO: some scheduling functions might be needed as argument, e.g

        add_idle: (unit -> bool) -> unit

        that will allow to install a handler when context is idle

        add_timeout: ms:int -> (unit -> bool) -> unit

        that will allow to install a handler when a timeout of ms
        milliseconds occurs

        in both cases, the bool returned indicates whether the handler
        should be removed or not

        the parameter OBSERVER could also be used for that purpose

    *)

    (* 
  val save_session : unit -> unit
    (** enforces to save the session state on disk. *)
       this is not necessary since the session manager handles this itself
       using add_timeout *)

  val add_file : string -> unit
    (** adds a new file in the proof session
    *)

  val reload_files : unit -> unit 
    (** reloads all the files in the state, and performs the proper
        mergind of old proof attemps and transformations *)

(*****************************)
(*                           *)
(*      actions              *)
(*                           *)
(*****************************)

(* attempt a new proof using an external prover *)

  val add_proof_attempt : goal  -> unit
    (** TODO: proper arguments missing *)

  val add_transformation : goal -> unit
    (** TODO: proper arguments missing *)

  val remove_proof_attempf : proof_attempt -> unit

  val remove_transformation : transf -> unit

  val clean : any -> unit
    (** [clean a] removes failed attempts below [a] where
        other successful attempts exist *)

  val redo_obsolete : any -> unit
    (** [redo_obsolete a] rerun obsolete proofs below [a] *)




(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
