(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Session_itp

(** State of a proof *)
type proof_attempt_status =
    | Unedited (** editor not yet run for interactive proof *)
    | JustEdited (** edited but not run yet *)
    | Interrupted (** external proof has never completed *)
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

val print_status : Format.formatter -> proof_attempt_status -> unit

type transformation_status = TSscheduled | TSdone  | TSfailed

val print_trans_status : Format.formatter -> transformation_status -> unit

module type Scheduler = sig

    (** Any module of this signature should implement a scheduler,
    that allows the register functions to call, and call them
    depending on some time constraints: after a given delay, or simply
    when there is no more tasks with higher priority. *)

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

type controller = private
  { mutable controller_session : Session_itp.session;
    controller_env : Env.env;
    controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
  }

val create_controller : Env.env -> Session_itp.session -> controller

module Make(S : Scheduler) : sig

val schedule_proof_attempt :
  controller ->
  proofNodeID ->
  Whyconf.prover ->
  limit:Call_provers.resource_limit ->
  callback:(proof_attempt_status -> unit) -> unit
(** [schedule_proof_attempt s id p ~timelimit ~callback] schedules a
   proof attempt for a goal specified by [id] with the prover [p] with
   time limit [timelimit]; the function [callback] will be called each
   time the proof attempt status changes. Typically at Scheduled, then
   Running, then Done. If there is already a proof attempt with [p] it
   is updated. *)

val schedule_transformation :
  controller ->
  proofNodeID ->
  string ->
  trans_arg list ->
  callback:(transformation_status -> unit) -> unit
(** [schedule_transformation c id cb] schedules a transformation for a
   goal specified by [id]; the function [cb] will be called each time
   the transformation status changes. Typically at Scheduled, then
   Done tid.*)

val add_file : controller -> ?format:Env.fformat -> string -> unit
(** [add_file_to_session cont ?fmt fname] parses the source file
    [fname] and add the resulting theories to the session of [cont] *)

val reload_files : controller -> unit
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

  - TODO: the presence of obsolete goals should be returned somehow by
    that function, as the presence of unmatch old theories or goals

 *)

end
