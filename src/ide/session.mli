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

(** {Prover's data} *)
type prover_data = private
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }
    (** record of necessary data for a given external prover *)

val get_prover_data : 
  Env.env -> Util.Mstr.key -> Whyconf.config_prover ->
  prover_data Util.Mstr.t -> prover_data Util.Mstr.t
  (** loads all provers from the current configuration *)

(** {Transformation's data} *)
type transformation_data 
  (** record data for transformations *)

val transformation_id : transformation_data -> string
  (** Why3 name of a transformation *)

val lookup_transformation : Env.env -> string -> transformation_data
  (** returns a transformation from its Why3 name *)

(** {Proof attempts} *)
type proof_attempt_status = private
    | Undone
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

(** {Observers signature} *)
module type OBSERVER = sig

  type key
    (** type key allowing to uniquely identify an element of
	of session: a goal, a transformation, a proof attempt,
	a theory or a file. See type [any] below *)

  val create: ?parent:key -> unit -> key
    (** returns a fresh key, a new child of the given parent if any *)

  val remove: key -> unit
    (** removes a key *)

  val timeout: ms:int -> (unit -> bool) -> unit
    (** a handler for functions that must be called after a given time
	elapsed, in milliseconds. When the given function returns
	true, it must be rescheduled *)

  val idle: (unit -> bool) -> unit
    (** a handler for a delayed function, that can be called when
	there is nothing else to do. When the given function returns
	true, it must be rescheduled *)

end

(** {Main functor} *)
module Make(O: OBSERVER) : sig

(** {static state of a session} *)

  type goal
    (** a goal *)

  type transf = private
      { transf : transformation_data;
	parent_goal : goal;
	mutable transf_proved : bool;
        transf_key : O.key;
        mutable subgoals : goal list;
      }
    (** a transformation of a given goal *)

  val goal_name : goal -> string
  val goal_expl : goal -> string
  val get_task : goal -> Task.task
  val goal_key : goal -> O.key
  val goal_proved : goal -> bool
  val transformations : goal -> (string, transf) Hashtbl.t

  type proof_attempt = private
      { prover : prover_data;
        proof_goal : goal;
        proof_key : O.key;
        mutable proof_state : proof_attempt_status;
        mutable proof_obsolete : bool;
        mutable edited_as : string;
      }
    (** a proof attempt for a given goal *)

  type theory 
    (** a theory, holding a collection of goals *)

  val theory_name : theory -> string
  val get_theory : theory -> Theory.theory
  val theory_key : theory -> O.key
  val verified : theory -> bool
  val goals : theory -> goal list

  type file = private
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
    env:Env.env ->
    provers:prover_data Util.Mstr.t ->
    init:(O.key -> any -> unit) ->
    notify:(any -> unit) -> string -> unit
    (** starts a new proof session, using directory given as argument 
        this reloads the previous session database if any.

        Opening a session must be done prior to any other actions.
        And it cannot be done twice.

	the [init] function is a function that will be called at each
	creation of element of the state

	the [notify] function is a function that will be called at each
	update of element of the state
    *)

  val maximum_running_proofs : int ref

  val save_session : unit -> unit
    (** enforces to save the session state on disk. 
	this it supposed to be called only at exit, 
	since the session manager also performs automatic saving 
	some time to time *)

  val file_exists : string -> bool

  val add_file : string -> unit
    (** [add_file adds the file [f] in the proof session,
	the file name must be given relatively to the session dir
	given to [open_session] *)


  val get_all_files : unit -> file list

  (* TODO
    val reload_files : unit -> unit 
  (** reloads all the files in the state, and performs the proper
    merging of old proof attemps and transformations *)
*)

(*****************************)
(*                           *)
(*      actions              *)
(*                           *)
(*****************************)

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

  val replay : 
    obsolete_only:bool -> 
    context_unproved_goals_only:bool -> any -> unit
    (** [replay a] reruns proofs under [a] 
        if obsolete_only is set then does not rerun non-obsolete proofs
        if context_unproved_goals_only is set then reruns only proofs with result was 'valid'
    *)

(*
TODO

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
