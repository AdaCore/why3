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

type transformation_status = TSscheduled of transID | TSdone of transID | TSfailed

module type Scheduler = sig
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit
end


module Make(S : Scheduler) : sig

val schedule_proof_attempt :
  session ->
  proofNodeID ->
  Whyconf.prover ->
  timelimit:int ->
  callback:(proof_attempt_status -> unit) -> unit
(** [schedule_proof_attempt s id p tl cb] schedules a proof attempt for
   a goal specified by [id] with the prover [p] with time limit [tl];
   the function [cb] will be called each time the proof attempt status
   changes. Typically at Scheduled, then Running, then Done. If there
   is already a proof attempt with [p] it is updated. *)

val schedule_transformations :
  session ->
  proofNodeID ->
  string ->
  trans_arg list ->
  callback:(transformation_status -> unit) -> unit
(** [schedule_transformations s id cb] schedules a transformation for a
   goal specified by [id]; the function [cb] will be called each time
   the transformation status changes. Typically at Scheluded, then
   Done tid.*)

val add_file_to_session :
  Env.env -> session -> ?format:Env.fformat -> string -> unit
(** [add_file_to_session env s ?fmt fname] parses the source file
    [fname] and add the resulting theories to the session [s] *)

val reload_session_files : session -> unit
(** reload the given session with the given environment :
    - the files are reloaded
    - apply again the transformation
    - if some goals appear try to find to which goal
    in the given session it corresponds.

    The last case meant that the session was obsolete.
    It is authorized if [allow_obsolete] is [true],
    otherwise the exception {!OutdatedSession} is raised.
    If the session was obsolete is indicated by
    the second result.
    If the merge generated new unpaired goals is indicated by
    the third result.

    raises [OutdatedSession] if the session is obsolete and
    [allow_obsolete] is false
*)

end
