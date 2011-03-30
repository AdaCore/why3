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


open Why

type prover_data = private
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }

val get_prover_data : 
  Env.env -> Util.Mstr.key -> Whyconf.config_prover ->
  prover_data Util.Mstr.t -> prover_data Util.Mstr.t

(* transformations *)
type transformation_data 

val transformation_id : transformation_data -> string

val lookup_transformation : Env.env -> string -> transformation_data

type proof_attempt_status = private
    | Undone
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

module type OBSERVER = sig

  type key
  val create: ?parent:key -> unit -> key
  val remove: key -> unit

  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit

end

module Make(O: OBSERVER) : sig

(*****************************)
(*                           *)
(* static state of a session *)
(*                           *)
(*****************************)

  type proof_attempt = private
      { prover : prover_data;
        proof_goal : goal;
        proof_key : O.key;
        mutable proof_state : proof_attempt_status;
        mutable proof_obsolete : bool;
        mutable edited_as : string;
      }

  and goal_parent =
    | Parent_theory of theory
    | Parent_transf of transf

  and goal = private
      { goal_name : string;
	goal_expl : string option;
	parent : goal_parent;
        task: Task.task;
        goal_key : O.key;
        mutable proved : bool;
        external_proofs: (string, proof_attempt) Hashtbl.t;
        transformations : (string, transf) Hashtbl.t;
      }

  and transf = private
      { transf : transformation_data;
	parent_goal : goal;
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

  val open_session : 
    init:(O.key -> any -> unit) ->
    notify:(any -> unit) -> string -> unit
    (** starts a new proof session, using directory given as argument 
        this reloads the previous session if any.

        Opening a session must be done prior to any other actions.
        And it cannot be done twice.

	the [init] function is a function that will be called at each
	creation of element of the state

	the [notify] function is a function that will be called at each
	update of element of the state
    *)

  val maximum_running_proofs : int ref

    (* 
  val save_session : unit -> unit
    (** enforces to save the session state on disk. *)
       this is not necessary since the session manager handles this itself
       using add_timeout *)

  val file_exists : string -> bool

  val add_file : string -> Theory.theory Theory.Mnm.t -> unit
    (** [add_file f ths] adds a new file in the proof session, that is
	a collection of name [f] of theories [ths] *)


  val get_all_files : unit -> file list

  (*
    val reload_files : unit -> unit 
  (** reloads all the files in the state, and performs the proper
    merging of old proof attemps and transformations *)
*)

(*****************************)
(*                           *)
(*      actions              *)
(*                           *)
(*****************************)

(*
  val apply_transformation : 
    callback:('a -> 'b) -> 'a Why.Trans.trans -> Why.Task.task -> 'b

  val apply_transformation_l : 
    callback:('a -> 'b) -> 'a Why.Trans.trans -> Why.Task.task -> 'b
*)

val apply_transformation : callback:(Task.task list -> unit) ->
  transformation_data -> Task.task -> unit

  val run_prover : context_unproved_goals_only:bool -> 
    prover_data -> any -> unit
    (** [run_prover p a] runs prover [p] on all goals under [a] *)

  val transform : context_unproved_goals_only:bool -> 
    transformation_data -> any -> unit
    (** [apply_transformation tr a] applies transformation [trp] 
	on all goals under [a] *)

  val edit_proof : 
    default_editor:string -> project_dir:string -> proof_attempt -> unit

  val replay : context_unproved_goals_only:bool -> any -> unit
    (** [replay a] reruns all valid but obsolete proofs under [a] *)

(*


  val remove_proof_attempt : proof_attempt -> unit

  val remove_transformation : transf -> unit

  val clean : any -> unit
    (** [clean a] removes failed attempts below [a] where
        there at least one successful attempt or transformation *)

    *) 
end



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
