(* This module is the Database for checks and goals. It also deals with the
   better part of scheduling of VCs.

   A check is something to be proved in Ada, say, a range check. A
   check is defined by an explanation (check kind + Ada location). This is the
   Gnat_expl.check type.

   A goal is a VC that will be sent to Alt-Ergo. In general, there will be many
   goals for each check. Each goal has a trace (list of locations).

   This module has the following functionality:
      - It answers queries to get the goals of a check and the
        check of a goal.
      - It supports scheduling by providing a "next" function that will by
      little chunks return all goals associated to a check.
      - It allows registering prover results and keeps track of the status of
        a check.
      - It defines the scheduler and initializes it, and all the goals,
        correctly.
*)

open Why3

type status =
   | Proved
   | Not_Proved
   | Work_Left
   | Counter_Example
(* These are the possible statuses of a check.
   [Proved] means that all goals of that check are proved.
   [Not_Proved] means that a proof attempt for a goal of the check that
               cannot (or should not) be further simplified has failed.

   In both cases, there is no more work to do, and we can issue a message to
   the user.

   [Work_Left] means that we don't know yet whether the check is proved or
               not, this means that all subgoals were proved up to now or if
               unproved could be further simplified, but there is some work
               left.
   [Counter_Example] means that the check cannot be proved and the
               counterexample should be generated.
*)

type subp
(* An object of type "subp" represents all checks for a given Ada
   subprogram. *)

(* various possibilities to add checks and goals to the database, and the
   "interesting" bit *)

type goal_id = Session_itp.proofNodeID
(* This is the type of identifier of goal. They can be queried from the session
   through Session_itp functions *)

val add_to_check : Gnat_expl.vc_info -> goal_id -> unit
(* register the goal with the given check. If this is the
   first time we register a goal for given check, the check is
   registered as well. Only do the registering if the check is to be
   discharged (ie, if the --limit-subp / --limit-line directives apply). *)

val set_not_interesting : goal_id -> unit
(* Goals can be not interesting, when they are trivial *)

val is_not_interesting : goal_id -> bool
val is_interesting : goal_id -> bool
(* query the "interesting" bit *)

val add_trivial_proof : Session_itp.session -> goal_id -> unit

val get_check_of_goal : goal_id -> Gnat_expl.check
(* get the check associated with a goal_id *)
val get_extra_info   : goal_id -> Gnat_expl.extra_info

(* Scheduling and proof *)
val next : Gnat_expl.check -> goal_id list
(* For a check, successive calls of [next] will return all goal_ids
   associated to the check, by chunks of size Gnat_config.parallel. [] is
   returned if no goal_ids are left. One can add new goal_ids to a check at any
   time. *)


(* Auxiliary functions *)

val iter : (Gnat_expl.check -> unit) -> unit
(* iterate over all registered checks *)

val iter_leaf_goals :
    Session_itp.session -> subp ->
      (Session_itp.proofNodeID -> unit) -> unit
(* iterate over all VCs of a subprogram. The callback will get an individual VC
   and the subp entity of the VC *)

val all_provers_tried : Session_itp.session -> goal_id -> bool
(* check whether an existing valid proof attempt exists for the goal_id, for all
   requested provers *)

val check_status : Gnat_expl.check -> status
(* query the status of the check *)

val ce_goal : Gnat_expl.check -> goal_id option

val init_cont : unit -> Controller_itp.controller
(* Makes a new controller with session *)

val clear : unit -> unit
(* delete all info from the database, except for the session tree itself *)

module GoalSet : sig
   (* module to provide mutable sets on goals *)
   type t
   val empty    : unit -> t
   val is_empty : t -> bool
   val add      : t -> goal_id -> unit
   val remove   : t -> goal_id -> unit
   val choose   : t -> goal_id
   val mem      : t -> goal_id -> bool
   val count    : t -> int
   val reset    : t -> unit
   val iter     : (goal_id -> unit) -> t -> unit
   val exists   : (goal_id -> bool) -> t -> bool
   val for_all  : (goal_id -> bool) -> t -> bool
end

module Make (S: Controller_itp.Scheduler) : sig

val register_result : Controller_itp.controller -> goal_id -> bool -> Gnat_expl.check * status
(* Register the result of a prover for a given goal_id, and return the updated
 * status of the check, as well as the check itself *)

val schedule_goal :
    callback:(Session_itp.proofAttemptID -> Controller_itp.proof_attempt_status -> unit) ->
    Controller_itp.controller -> goal_id -> unit
(* schedule a goal for proof with default prover and
   default timeout. The function returns immediately.
   @param cntexample indicates whether the prover should be queried for
     a counterexample.
*)

val schedule_goal_with_prover :
  callback:(Session_itp.proofAttemptID -> Controller_itp.proof_attempt_status -> unit) ->
  Controller_itp.controller -> goal_id -> Whyconf.prover -> unit
(* schedule a goal for proof with given prover and
   default timeout. The function returns immediately.
*)

val save_session : Controller_itp.controller -> unit
(* save the session; should be called on exit. *)

(* dealing with a main goal *)

val iter_subps : Controller_itp.controller -> (subp -> unit) -> unit
(* iterate over all subprograms. *)

val init_subp_vcs : Controller_itp.controller -> subp -> unit
(* init the vcs for a given subp *)

module Save_VCs : sig
   (* Provide saving of VCs, traces *)

   val extract_stats :
     Controller_itp.controller -> Gnat_expl.check -> Gnat_report.stats * int
   (* The second field of the return tuple is the number of goal proved by a
      transformation that is not trivial_true (Checker prover). *)

   val vc_file : goal_id -> string
   (* get the file name for a given goal *)

   val check_to_json : Session_itp.session -> Gnat_expl.check -> Json_base.json

   val unproved_prover_answer :
      Session_itp.session ->Session_itp.proofNodeID option -> Gnat_expl.check -> Gnat_expl.unproved_status
   (* get the unproved status for a given goal (proofNodeID).
      If the goal is None, use the check instead. *)
end

val all_split_leaf_goals : unit -> unit
(* special-purpose function for "all_split" mode (see gnat_config.mli),
   where all split VCs are saved to disk, and no prover is called. *)

val goal_has_splits : Session_itp.session -> goal_id -> bool

val is_ce_goal : Session_itp.session -> Session_itp.proofNodeID -> bool
val is_valid_not_ce: Session_itp.session -> Session_itp.proofNodeID -> bool

val session_proved_status : Controller_itp.controller -> Gnat_expl.check -> bool
(* check the proof status of an check by looking at the verified/not
   verified status of its VCs in the session *)

val remove_all_valid_ce_attempt: Session_itp.session -> unit
(* Removes all valid ce attempt that pollutes the session
   ??? We may want to report this information to explain lack of counterexamples
   or try greater timeout ? *)

val session_find_unproved_pa :
    Controller_itp.controller -> Gnat_expl.check -> Session_itp.proofAttemptID option
(* find the first unproved (not obsolete) proof attempt in a session which is
 *  in subforest of check. *)

val session_find_ce_pa :
    Controller_itp.controller -> Gnat_expl.check -> Session_itp.proofAttemptID option
(* Find the proof attempt related to the counter example, if any *)

val session_find_unproved_goal :
    Controller_itp.controller -> Gnat_expl.check -> Session_itp.proofNodeID option
(* find the first unproved goal in a session (in subforest of check) *)


val replay : Controller_itp.controller -> unit

end
