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

(** Controller to run provers and transformations asynchronously on goals of a session
 *)

open Session_itp

(** {2 State of a proof or transformation in progress} *)

type proof_attempt_status =
    | Unedited (** editor not yet run for interactive proof *)
    | JustEdited (** edited but not run yet *)
    | Interrupted (** external proof has never completed *)
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)
    | Uninstalled of Whyconf.prover (** prover is uninstalled *)

val print_status : Format.formatter -> proof_attempt_status -> unit

type transformation_status =
    TSscheduled
  | TSdone of transID
  | TSfailed of (proofNodeID * exn)

val print_trans_status : Format.formatter -> transformation_status -> unit

type strategy_status = STSgoto of proofNodeID * int | STShalt

val print_strategy_status : Format.formatter -> strategy_status -> unit

exception Noprogress

(** {2 Signature for asynchronous schedulers} *)

(** Default delay for the scheduler timeout *)
val default_delay_ms: int

module type Scheduler = sig

    (** Any module of this signature should implement a scheduler,
    that allows the register functions to call, and call them
    depending on some time constraints: after a given delay, or simply
    when there is no more tasks with higher priority. *)

    val multiplier: int
    (** Number of allowed task given to why3server is this number times the
        number of allowed proc on the machine.
    *)

    val timeout: ms:int -> (unit -> bool) -> unit
    (** [timeout ~ms f] registers the function [f] as a function to be
    called every [ms] milliseconds. The function is called repeatedly
    until it returns false. the [ms] delay is not strictly guaranteed:
    it is only a minimum delay between the end of the last call and
    the beginning of the next call.  Several functions can be
    registered at the same time. *)

    val idle: prio:int -> (unit -> bool) -> unit
    (** [idle prio f] registers the function [f] as a function to be
    called whenever there is nothing else to do. Several functions can
    be registered at the same time.  Several functions can be
    registered at the same time. Functions registered with higher
    priority will be called first. *)

end


(** {2 Controllers} *)

type controller = private
  { mutable controller_session : Session_itp.session;
    controller_config : Whyconf.config;
    controller_env : Env.env;
    controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
    controller_strategies : (string * string * Strategy.instruction array) Stdlib.Hstr.t;
  }

val create_controller: Whyconf.config -> Env.env -> Session_itp.session -> controller
(** creates a controller for the given session.
    The config and env is used to load the drivers for the provers. *)

val print_session : Format.formatter -> controller -> unit



val reload_files : controller -> use_shapes:bool -> bool * bool
(** reload the files of the given session:

  - each file is parsed again and theories/goals extracted from it. If
    some syntax error or parsing error occurs, then the corresponding
    file is kept in the session, without any corresponding new theory,
    that is as if it was an empty file (TODO: such errors should be
    returned somehow by the function [reload_files])

  - each new theory is associated to a theory of the former session if
    the names match exactly. In case of no match:

    . a new theory and its goals appear without any proof attempts in
      it in the new session

    . an unmatched old theory is kept in the new session together with
      its former goals, proof attempts and transformations, but
      without any tasks associated to goals and subgoals.

  - within a new theory with a corresponding old theory, each goal is
    in turn associated to a former goal if possible. the match is done
    either on the goal name, or if no name match exactly, on the goal
    shape.

    . a new goal without match is added with an empty set of proof
      attempts and transformations

    . an old goal without match is kept with all its former proof
      attempts and transformations, but no task is associated to it,
      neither to its subgoals.

  - on each new goal that has a matching old goal, old proof
    attempts are attached, with the status obsolete if the task has
    changed

  - on each new goal that has a matching old goal, old
    transformations are attached, and applied to the task, the
    generated subgoals are in turn matched to the old sub-goals, in
    the same manner as for goals in a theory

    . an old sub-goals without a match is kept with all its former
      proof attempts and transformations, but no task is associated to
      it, neither to its subgoals.

*)

val add_file : controller -> ?format:Env.fformat -> string -> unit
(** [add_fil cont ?fmt fname] parses the source file
    [fname] and add the resulting theories to the session of [cont] *)

val remove_subtree: controller -> notification:notifier -> removed:notifier ->
   any -> unit
(** Mapping to Session_itp.remove_subtree. Used for code using Why3's API *)

val get_undetached_children_no_pa: Session_itp.session -> any -> any list


(** {2 Scheduled jobs} *)

module Make(S : Scheduler) : sig

val set_max_tasks : int -> unit
(** sets the maximum number of proof tasks that can be running at the
    same time. Initially set to 1. *)

val register_observer : (int -> int -> int -> unit) -> unit
(** records a hook that will be called with the number of waiting
    tasks, scheduled tasks, and running tasks, each time these numbers
    change *)

(* TODO
val register_notifier : (any -> unit) -> unit
(** records a hook that will be called each time a node change status *)
 *)


val interrupt : unit -> unit
(** discards all scheduled proof attempts or transformations, including
    the ones already running *)

val schedule_proof_attempt :
  ?proof_script:string ->
  controller ->
  proofNodeID ->
  Whyconf.prover ->
  counterexmp:bool ->
  limit:Call_provers.resource_limit ->
  callback:(proofAttemptID -> proof_attempt_status -> unit) ->
  notification:notifier -> unit
(** [schedule_proof_attempt c id p ~timelimit ~callback ~notification] schedules a
   proof attempt for a goal specified by [id] with the prover [p] with
   time limit [timelimit]; the function [callback] will be called each
   time the proof attempt status changes. Typically at Scheduled, then
   Running, then Done. If there is already a proof attempt with [p] it
   is updated. *)

val schedule_edition :
  controller ->
  proofNodeID ->
  Whyconf.prover ->
  no_edit: bool ->
  do_check_proof: bool ->
  ?file: string ->
  callback:(proofAttemptID -> proof_attempt_status -> unit) ->
  notification:notifier -> unit
(** [schedule_edition c id pr ~no_edit ~do_check_proof ?file ~callback
      ~notification]
    runs the editor for prover [pr] on proofnode [id] on a file automatically
    generated in [file] (or created path). It will runs callback each time
    the proof status changes and notification will be called each time a
    change is made to the proof_state (in the whole proof tree of the session).
    If no_edit is true, the editor is not launched but the proofattempt is still
    created.
    If do_check_proof is true, the proof is replayed in the callback (it avoids
    having obsolete proofs when exiting the ide).
*)

val schedule_transformation :
  controller ->
  proofNodeID ->
  string ->
  string list ->
  callback:(transformation_status -> unit) ->
  notification:notifier -> unit
(** [schedule_transformation c id cb] schedules a transformation for a
   goal specified by [id]; the function [cb] will be called each time
   the transformation status changes. Typically at Scheduled, then
   Done tid.*)

val run_strategy_on_goal :
  controller ->
  proofNodeID ->
  Strategy.t ->
  counterexmp:bool ->
  callback_pa:(proofAttemptID -> proof_attempt_status -> unit) ->
  callback_tr:(string -> string list -> transformation_status -> unit) ->
  callback:(strategy_status -> unit) ->
  notification:notifier -> unit
(** [run_strategy_on_goal c id strat] executes asynchronously the
    strategy [strat] on the goal [id].  [callback_pa] is called for
    each proof attempted (as in [schedule_proof_attempt]) and
    [callback_tr] is called for each transformation applied (as in
    [schedule_transformation]). [callback] is called on each step of
    execution of the strategy.  *)

val clean_session: controller -> removed:notifier -> unit
(** Remove each proof attempt or transformation that are below proved
    goals, that are either obsolete or not valid. The [removed]
    notifier is called on each removed node.  *)

val mark_as_obsolete:
  notification:notifier ->
  controller -> any -> unit

(* [copy_paste c a b] try to copy subtree originating at node a to node b *)
val copy_paste:
    notification:notifier ->
    callback_pa:(proofAttemptID -> proof_attempt_status -> unit) ->
    callback_tr:(string -> string list -> transformation_status -> unit) ->
    controller -> any -> any -> unit

val copy_detached:
    copy:(parent:any -> any -> unit) ->
    controller -> any -> unit

type report =
  | Result of Call_provers.prover_result * Call_provers.prover_result
        (** Result(new_result,old_result) *)
  | CallFailed of exn
  | Replay_interrupted
  | Prover_not_installed
  | Edited_file_absent of string
  | No_former_result of Call_provers.prover_result
(** Type for the reporting of a replayed call *)

(* Callback for the report printing of replay
   TODO to be removed when we have a better way to print the result of replay *)
val replay_print:
    Format.formatter ->
      (proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list ->
        unit

val replay:
    ?obsolete_only:bool ->
    ?use_steps:bool ->
    controller ->
    callback:(proofAttemptID -> proof_attempt_status -> unit) ->
    notification:notifier ->
    final_callback:
      ((proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list
            -> unit) ->
    unit
(** This function reruns all the proofs of the session, and produces a report
    comparing the results with the former ones.

    The proofs are replayed asynchronously, and the states of these proofs are
    notified via [callback] similarly as for [schedule_proof_attempt].

    The session state is changed, all changes are notified via the
    callback [notification]

    When finished, call the callback [final_callback] with the report,
a list of 4-uples [(goalID, prover, limits, report)]

    When obsolete_only is set, only obsolete proofs are replayed (default)

    When use_steps is set, replay use the recorded number of proof
    steps (not set by default)

 *)


val bisect_proof_attempt:
  notification:notifier -> controller -> proofAttemptID -> unit

end
