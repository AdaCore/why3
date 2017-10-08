(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Scheduling operations on sessions and calls to provers *)

(** {2 One module for calling callback when it's time to} *)

module Todo : sig
  type ('a,'b) todo

  val create : 'a -> ('a -> 'b -> 'a) -> ('a -> unit) -> ('a,'b) todo
    (** create init step callback *)

  val start : ('a,'b) todo -> unit
  (** one task is started *)

  val stop : ('a,'b) todo -> unit
  (** one task is stopped without information *)

  val _done : ('a,'b) todo -> 'b -> unit
  (** one task is stopped with information *)

end

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

  val uninstalled_prover :
    key env_session -> Whyconf.prover -> Whyconf.prover_upgrade_policy
    (** When a prover must be called on a task but it is currently
        not installed, what policy to apply *)

end

(** {2 Main functor} *)

module Make(O: OBSERVER) : sig
  (** A session, with the environment, and the configuration *)

  (** {2 Scheduler} *)

  type t (** the scheduler environment *)

  val set_maximum_running_proofs : int -> t -> unit

  val init : int -> t
  (** [init max] *)

(* used by why3session_run, but it should not as it is a low-level scheduler
  function *)
  val schedule_any_timeout: t -> (unit -> bool) -> unit
(** run it when an action slot/worker/cpu is available. Reschedule it if it
    return true *)


  (** {2 Save and load a state} *)

  val update_session :
    allow_obsolete:bool ->
    release:bool ->
    use_shapes:bool ->
    'oldkey session ->
    Env.env -> Whyconf.config ->
    O.key env_session * bool * bool
  (**
     Same as {!Session.update_session} except initialization is done.
    *)

  val add_file :
    O.key env_session -> ?format:string -> string -> O.key Session.file
    (** [add_file es f] adds the file with filename [f] in the proof
        session, the file name must be given relatively to the session
        dir given to [open_session]
    *)

(** {2 Actions} *)

  val run_prover :
    O.key env_session -> t ->
    context_unproved_goals_only:bool ->
    cntexample : bool ->
    limit : Call_provers.resource_limit ->
    Whyconf.prover -> O.key any -> unit
    (** [run_prover es sched p a] runs prover [p] on all goals under [a]
        the proof attempts are only scheduled for running, and they
        will be started asynchronously when processors are available.

        ~context_unproved_goals_only indicates if prover must be run
        on already proved goals or not
	~cntexample indicates if prover should be asked to get counter-example
	model
    *)


  val run_external_proof :
    O.key env_session -> t ->
    ?cntexample : bool ->
    ?callback:(O.key proof_attempt -> proof_attempt_status -> unit) ->
    O.key proof_attempt -> unit
  (** [run_external_proof es sched ?cntexample ?callback p] reruns an existing
      proof attempt [p]

      ~cntexample indicates if prover should be asked to get counter-example
	model
  *)


  type run_external_status =
    | Starting
    | MissingProver
    | MissingFile of string
    | StatusChange of proof_attempt_status

  val run_external_proof_v3 :
    use_steps:bool ->
    O.key Session.env_session -> t -> O.key Session.proof_attempt ->
    ?cntexample : bool ->
    (O.key Session.proof_attempt -> Whyconf.prover ->
     Call_provers.resource_limit -> Call_provers.prover_result option -> run_external_status -> unit) ->
     unit
  (** [run_external_proof_v3 env_session sched pa ?cntexample callback] the
      callback is applied with [callback pa p limits old_result
      status]. run_external_proof_v3 don't change the existing proof
      attempt just can add new by O.uninstalled_prover. Be aware since
      the session is not modified there is no test to see if the
      proof_attempt had already been started

      ?cntexample indicates if prover should be asked to get counter-example
	model
  *)


  val prover_on_goal :
    O.key env_session -> t ->
    ?callback:(O.key proof_attempt -> proof_attempt_status -> unit) ->
    ?cntexample : bool ->
    limit : Call_provers.resource_limit ->
    Whyconf.prover -> O.key goal -> unit
  (** [prover_on_goal es sched ?cntexample ?timelimit p g] same as
      {!redo_external_proof} but creates or reuses existing proof_attempt

      ?cntexample indicates if prover should be asked to get counter-example
	model
  *)


  val cancel_scheduled_proofs : t -> unit
    (** cancels all currently scheduled proof attempts.
        note that the already running proof attempts are not
        stopped, the corresponding processes must terminate
        by their own. *)


  val transform_goal :
    O.key env_session -> t ->
    ?keep_dumb_transformation:bool ->
    ?callback:(O.key transf option -> unit) ->
    string -> O.key goal -> unit
    (** [transform es sched tr g] applies registered
        transformation [tr] on the given goal.

        If [keep_dumb_transformation] is false (default)
        and the transformation gives one task equal to [g]
        the transformation is not added (the callback is called with None).
        Otherwise the transformation is added and given to the callback.
    *)


  val transform :
    O.key env_session -> t ->
    context_unproved_goals_only:bool ->
    ?callback:(O.key transf option -> unit) ->
    string -> O.key any -> unit
    (** [transform es sched tr a] applies registered
        transformation [tr] on all leaf goals under [a].

        [~context_unproved_goals_only] indicates if the transformation
        must be applied also on alreadt proved goals *)

  val edit_proof :
    cntexample:bool ->
    O.key env_session -> t ->
    default_editor:string ->
    O.key proof_attempt -> unit
  (** edits the given proof attempt using the appropriate editor *)

  val edit_proof_v3 :
    cntexample:bool ->
    O.key env_session -> t ->
    default_editor:string ->
    callback:(O.key Session.proof_attempt ->  unit) ->
    O.key proof_attempt -> unit
  (** edits the given proof attempt using the appropriate editor but
      don't modify the session *)


  val cancel : O.key any -> unit
  (** [cancel a] marks all proofs under [a] as obsolete *)

  val remove_proof_attempt : O.key proof_attempt -> unit

  val remove_transformation : O.key transf -> unit

  val remove_metas : O.key metas -> unit

  val set_archive : O.key proof_attempt -> bool -> unit

  val clean : O.key any -> unit
    (** [clean a] removes failed attempts below [a] where
        there at least one successful attempt or transformation *)


  type report =
    | Result of Call_provers.prover_result * Call_provers.prover_result
        (** Result(new_result,old_result) *)
    | CallFailed of exn
    | Prover_not_installed
    | Edited_file_absent of string
    | No_former_result of Call_provers.prover_result

  val replay :
    O.key env_session -> t ->
    obsolete_only:bool ->
    context_unproved_goals_only:bool -> O.key any -> unit
  (** [replay es sched ~obsolete_only ~context_unproved_goals_only
        a] reruns proofs under [a] if [obsolete_only] is set then does
        not rerun non-obsolete proofs if [context_unproved_goals_only]
        is set then only rerun proofs whose previous answer was
        'valid' *)

  val check_all:
    ?release:bool -> (* Can all the goals be released at the end? def: false *)
    use_steps:bool -> (* Replay use recorded number of proof steps *)
    ?filter:(O.key proof_attempt -> bool) ->
    O.key env_session -> t ->
    callback:
      ((Ident.ident * Whyconf.prover * Call_provers.resource_limit * report) list
            -> unit) ->
    unit
  (** [check_all session callback] reruns all the proofs of the
        session, and reports for all proofs the current result and the
        new one (does not change the session state). When finished,
        calls the callback with the reports which are 4-uples [(goal
        name, prover, limits, report)] *)

  val play_all :
    O.key env_session -> t -> callback:(unit-> unit) ->
    limit:Call_provers.resource_limit -> Whyconf.prover list -> unit
    (** [play_all es sched l] runs every prover of list [l] on all
        goals and sub-goals of the session, with the given time limit.
        [callback] is called when all tasks are finished.
        Useful for benchmarking provers
    *)

  val schedule_proof_attempt:
    cntexample:bool ->
    limit:Call_provers.resource_limit ->
    ?old:string ->
    inplace:bool ->
    command:string ->
    driver:Driver.driver ->
    callback:(Session.proof_attempt_status -> unit) -> t -> Task.task -> unit

  val convert_unknown_prover : O.key env_session -> unit
    (** Same as {!Session_tools.convert_unknown_prover} *)

  val run_strategy_on_goal:
    ?intermediate_callback: (unit -> unit) ->
    ?final_callback: (unit -> unit) ->
    O.key Session.env_session -> t ->
    Strategy.t -> O.key Session.goal -> unit

  val run_strategy:
    O.key Session.env_session -> t ->
    context_unproved_goals_only:bool ->
    Strategy.t -> O.key Session.any -> unit

end


(** A functor (a state is hidden) that provide a working scheduler
    and which can be used as base for an OBSERVER *)
module Base_scheduler (X : sig end) : sig

  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit
  val verbose : bool ref
  val notify_timer_state : int -> int -> int -> unit
  (** These functions have the properties required by OBSERVER *)

  val main_loop : unit -> unit
  (** [main_loop ()] run the main loop. Run the timeout handler and the
      the idle handler registered until the two of them are done. Nothing is run
      until this function is called *)

end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
