(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

(** Proof sessions *)

open Session

(** {2 Observers signature} *)

module type OBSERVER = sig

  type key
    (** type key allowing to uniquely identify an element of
        of session: a goal, a transformation, a proof attempt,
        a theory or a file. See type [any] below *)

  val create: ?parent:key -> unit -> key
    (** returns a fresh key, a new child of the given parent if any *)

  val remove: key -> unit
    (** removes a key *)

  val reset: unit -> unit
    (** deletes all keys *)

  val timeout: ms:int -> (unit -> bool) -> unit
    (** a handler for functions that must be called after a given time
        elapsed, in milliseconds. When the given function returns
        true, it must be rescheduled *)

  val idle: (unit -> bool) -> unit
    (** a handler for a delayed function, that can be called when
        there is nothing else to do. When the given function returns
        true, it must be rescheduled *)

  val notify_timer_state : int -> int -> int -> unit
    (** this function is called when timer state changes.
        The first arg is the number of tasks waiting.
        The second arg is the number of scheduled proof tasks.
        The third arg is the number of running proof tasks *)


  val init : key -> key any -> unit
    (** run after the creation *)

  val notify : key any -> unit
    (** notify modification of node of the session *)

end

(** {2 Main functor} *)

module Make(O: OBSERVER) : sig

  (** A session, with the environnement, and the configuration *)
  type t (** the scheduler environment *)

  val set_maximum_running_proofs : int -> t -> unit

  val init : int -> t
  (** [init max] *)

(** {2 static state of a session} *)


  (** {2 Save and load a state}      *)

  val update_session :
    allow_obsolete:bool ->
    'key session ->
    Env.env -> Whyconf.config ->
    O.key env_session * bool



    (** starts a new proof session, using directory given as argument
        this reloads the previous session database if any.

        Opening a session must be done prior to any other actions.
        And it cannot be done twice.

        the [notify] function is a function that will be called at each
        update of element of the state

        the [init] function is a function that will be called at each
        creation of element of the state

        raises [OutdatedSession] if [allow_obsolete] is false and any obsolete
        data for a goal is found in the session database

        raises [Failure msg] if the database file cannot be read correctly

        returns true if some obsolete goal was found (and
        [allow_obsolete] is true), false otherwise

    *)

  val add_file : O.key env_session -> string -> O.key Session.file
    (** [add_file f] adds the file [f] in the proof session,
        the file name must be given relatively to the session dir
        given to [open_session] *)

(** {2 Actions} *)

  val run_prover :
    O.key env_session -> t ->
    context_unproved_goals_only:bool ->
    timelimit:int -> prover -> O.key any -> unit
    (** [run_prover p a] runs prover [p] on all goals under [a]
        the proof attempts are only scheduled for running, and they
        will be started asynchronously when processors are available
    *)

  val cancel_scheduled_proofs : t -> unit
    (** cancels all currently scheduled proof attempts.
        note that the already running proof attempts are not
        stopped, the corresponding processes must terminate
        by their own. *)

  val transform :
    O.key env_session -> t ->
    context_unproved_goals_only:bool ->
    string -> O.key any -> unit
    (** [apply_transformation tr a] applies transformation [trp]
        on all goals under [a] *)

  val edit_proof :
    O.key env_session -> t ->
    default_editor:string -> project_dir:string ->
    O.key proof_attempt -> unit
    (** edit the given proof attempt using the appropriate editor *)

  val replay :
    O.key env_session -> t ->
    obsolete_only:bool ->
    context_unproved_goals_only:bool -> O.key any -> unit
    (** [replay a] reruns proofs under [a]
        if obsolete_only is set then does not rerun non-obsolete proofs
        if context_unproved_goals_only is set then reruns only proofs
        with result was 'valid'
    *)

  val cancel : O.key any -> unit
    (** [cancel a] marks all proofs under [a] as obsolete *)

  val remove_proof_attempt : O.key proof_attempt -> unit

  val remove_transformation : O.key transf -> unit

  val clean : O.key any -> unit
    (** [clean a] removes failed attempts below [a] where
        there at least one successful attempt or transformation *)


  type report =
    | Result of Call_provers.prover_result * Call_provers.prover_result
        (** Result(new_result,old_result) *)
    | CallFailed of exn
    | Prover_not_installed
    | No_former_result of Call_provers.prover_result

  val check_all:
    O.key env_session -> t ->
    callback:((Ident.ident * prover * report) list -> unit) -> unit
    (** [check_all ()] reruns all the proofs of the session, and reports
        all difference with the current state
        (does not change the session state)
        When finished, calls the callback with the list of failed comparisons,
        which are triples (goal name, prover, report)
    *)

  val convert_unknown_prover : O.key env_session -> unit

(*
  val reload_all: bool -> bool
    (** reloads all the files
        If for one of the file, the parsing or typing fails, then
        the complete old session state is kept, and an exception
        is raised

        raises [OutdatedSession] if [allow_obsolete] is false and any obsolete
        data for a goal is found in the session database

        returns true if some obsolete goal was found (and
        [allow_obsolete] is true), false otherwise

    *)

  val smoke_detector : smoke_detector ref
    (** Define if the smoke detector is used *)
*)
end



(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
