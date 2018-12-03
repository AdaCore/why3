(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
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
  | Undone   (** prover was never called *)
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | Interrupted (** external proof has never completed *)
  | Detached (** parent goal has no task, is detached *)
  | InternalFailure of exn (** external proof aborted by internal error *)
  | Uninstalled of Whyconf.prover (** prover is uninstalled *)
  | UpgradeProver of Whyconf.prover (** prover is upgraded *)
  | Removed of Whyconf.prover (** prover has been removed or upgraded *)

val print_status : Format.formatter -> proof_attempt_status -> unit

type transformation_status =
    TSscheduled
  | TSdone of transID
  | TSfailed of (proofNodeID * exn)
  (* We distinguish normal usage exception of transformation from fatal
     exception like assertion failure that should not be raised *)
  | TSfatal of (proofNodeID * exn)

val print_trans_status : Format.formatter -> transformation_status -> unit

type strategy_status = STSgoto of proofNodeID * int | STShalt
                     (* When a transformation fatally returns, we have to
                        fatally fail the strategy
                        [transformation_name, pid, exn] *)
                     | STSfatal of string * proofNodeID * exn

val print_strategy_status : Format.formatter -> strategy_status -> unit

(** {2 Signature for asynchronous schedulers} *)

(** Default delay for the scheduler timeout *)
val default_delay_ms: int

module type Scheduler = sig

    (** Any module of this signature should implement a scheduler,
    that allows the register functions to call, and call them
    depending on some time constraints: after a given delay, or simply
    when there is no more tasks with higher priority. *)

    val blocking: bool
    (** Set to true when the scheduler should wait for results of why3server
        (script), false otherwise (ITP which needs reactive scheduling) *)

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
    mutable controller_config : Whyconf.config;
    mutable controller_env : Env.env;
    controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
    controller_strategies : (string * string * string * Strategy.instruction array) Wstdlib.Hstr.t;
    controller_running_proof_attempts : unit Hpan.t;
  }

val create_controller: Whyconf.config -> Env.env -> Session_itp.session -> controller
(** creates a controller for the given session.
    The config and env is used to load the drivers for the provers. *)


val set_session_max_tasks : int -> unit
(** sets the maximum number of proof tasks that can be running at the
    same time. Initially set to 1. *)

val set_session_prover_upgrade_policy :
  controller -> Whyconf.prover -> Whyconf.prover_upgrade_policy -> unit


val print_session : Format.formatter -> controller -> unit



exception Errors_list of exn list

val reload_files : controller -> shape_version:int option -> bool * bool
(** [reload_files] returns a pair [(o,d)]: [o] true means there are
    obsolete goals, [d] means there are missed objects (goals,
    transformations, theories or files) that are now detached in the
    session returned.

  If parsing or typing errors occurs, a list of errors is raised
  inside exception Errors_list.

  The detailed process of reloading the files of the given session is
  as follows.

  - each file is parsed again and theories/goals extracted from it. If
    some syntax error or parsing error occurs, then the corresponding
    file is kept in the session, without any corresponding new theory,
    that is as if it was an empty file (detached mode)
    (those errors are returned as first component

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
(** [add_file cont ?fmt fname] parses the source file
    [fname] and add the resulting theories to the session of [cont].
    parsing or typing errors are raised inside exception [Errors_list]
 *)

val remove_subtree: notification:notifier -> removed:notifier ->
   controller -> any -> unit
(** remove a subtree of the session, taking care of not removing any
    proof attempt in progress. raise [RemoveError] if removal is not
    possible. *)

val get_undetached_children_no_pa: Session_itp.session -> any -> any list


(** {2 Scheduled jobs} *)

module Make(S : Scheduler) : sig

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
  controller ->
  proofNodeID ->
  Whyconf.prover ->
  ?save_to:string ->
  limit:Call_provers.resource_limit ->
  callback:(proofAttemptID -> proof_attempt_status -> unit) ->
  notification:notifier -> unit
(** [schedule_proof_attempt c id p ~timelimit ~callback ~notification] schedules a
   proof attempt for a goal specified by [id] with the prover [p] with
   time limit [timelimit]; the function [callback] will be called each
   time the proof attempt status changes. Typically at Scheduled, then
   Running, then Done. If there is already a proof attempt with [p] it
   is updated.
   [save_to] is used to give a location for the file generated for the prover
   ( *.smt2). With debug flag keep_vcs, the file are saved at this location.
*)

val schedule_edition :
  controller ->
  proofNodeID ->
  Whyconf.prover ->
  callback:(proofAttemptID -> proof_attempt_status -> unit) ->
  notification:notifier -> unit
(** [schedule_edition c id pr ~callback ~notification] runs the editor
    for prover [pr] on proofnode [id] on a file whose name is
    automatically generated. It will runs callback each time the proof
    status changes and notification will be called each time a change
    is made to the proof_state (in the whole proof tree of the
    session).  *)

val prepare_edition :
  controller -> ?file:string -> proofNodeID -> Whyconf.prover ->
  notification:notifier -> proofAttemptID * string * Call_provers.prover_result option
(** [prepare_edition c ?file id pr] prepare for editing the proof of
    node [id] with prover [pr]. The editor is not launched. The result
    is [(pid,name,res)] where [pid] is the node id the proof_attempt,
    [name] is the name of the file to edit, made relative to the
    session directory, and [res] is the former result if any. *)

exception TransAlreadyExists of string * string
exception GoalNodeDetached of proofNodeID

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

val clean: controller -> removed:notifier -> any option -> unit
(** Remove each proof attempt or transformation that are below proved
    goals, that are either obsolete or not valid. The [removed]
    notifier is called on each removed node.
    On None, clean is done on the whole session. *)

val mark_as_obsolete:
  notification:notifier ->
  controller -> any option -> unit

exception BadCopyPaste

(* [copy_paste c a b] try to copy subtree originating at node a to node b *)
val copy_paste:
    notification:notifier ->
    callback_pa:(proofAttemptID -> proof_attempt_status -> unit) ->
    callback_tr:(string -> string list -> transformation_status -> unit) ->
    controller -> any -> any -> unit


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
    valid_only:bool ->
    obsolete_only:bool ->
    ?use_steps:bool ->
    ?filter:(proof_attempt_node -> bool) ->
    controller ->
    callback:(proofAttemptID -> proof_attempt_status -> unit) ->
    notification:notifier ->
    final_callback:
      (bool ->
       (proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list
       -> unit) -> any: Session_itp.any option ->
    unit
(** This function reruns all the proofs of the session under the given any (None
    means the whole session), and produces a report comparing the results with
    the former ones.

    The proofs are replayed asynchronously, and the states of these proofs are
    notified via [callback] similarly as for [schedule_proof_attempt].

    The session state is changed, all changes are notified via the
    callback [notification]

    When finished, call the callback [final_callback] with a boolean
    telling if some prover was upgraded, and the report, a list of
    4-uples [(goalID, prover, limits, report)]

    When [obsolete_only] is set, only obsolete proofs are replayed (default)

    When [use_steps] is set, replay use the recorded number of proof
    steps (not set by default)

    When [filter] is set, only the proof attempts on which the filter
    returns true are replayed

 *)

exception CannotRunBisectionOn of proofAttemptID

val bisect_proof_attempt:
  callback_tr:(string -> string list -> transformation_status -> unit) ->
  callback_pa:(proofAttemptID -> proof_attempt_status -> unit) ->
  notification:notifier ->
  removed:notifier ->
  controller -> proofAttemptID -> unit
  (** [bisect_proof_attempt ~callback_tr ~callback_pa ~notification
                            ~removed cont id] runs a bisection process
      based on the proof attempt [id] of the session managed by [cont].

      The proof attempt [id] must be a successful one, otherwise,
      exception [CannotRunBisectionOn id] is raised.

      Bisection tries to remove from the context the largest number of
      definitions and axioms, using the `remove` transformation (bound
      to [Cut.remove_list]). It proceeeds by dichotomy of the
      context. Note that there is no garantee that the removed data at
      the end is globally maximal. During that process, [callback_tr]
      is called each time the `remove` transformation is added to the session,
      [callback_pa] is called each time the prover is called on a
      reduced task, [notification] is called when a proof node is
      created or modified, and [removed] is called when a node is
      removed.

   *)
end
