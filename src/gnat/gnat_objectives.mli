(* This module is the Database for objectives and goals. It also deals with the
   better part of scheduling of VCs.

   An objective is something to be proved in Ada, say, a range check. An
   objective is defined by an explanation (reason + Ada location).

   A goal is a VC that will be sent to Alt-Ergo. In general, there will be many
   goals for each objective. Each goal has a trace (list of locations).

   This module has the following functionality:
      - It answers queries to get the goals of an objective and the
        objective of a goal.
      - It supports scheduling by providing a "next" function that will by
      little chunks return all goals associated to an objective.
      - It allows registering prover results and keeps track of the status of
        an objective.
      - It defines the scheduler and initializes it, and all the goals,
        correctly.
*)

open Why3

type objective = Gnat_expl.check
(* an objective is identified by its check, which contains the check id and the
   kind of the check *)

type key = int

type goal = key Session.goal

type subp
(* An object of type "subp" represents all objectives for a given Ada
   subprogram. *)

(* various possibilities to add objectives and goals to the database, and the
   "interesting" bit *)

val add_to_objective : objective -> goal -> unit
(* register the goal with the given objective. If this is the
   first time we register a goal for given objective, the objective is
   registered as well. Only do the registering if the objective is to de
   discharged (ie, if the --limit-subp / --limit-line directives apply). *)

val set_not_interesting : goal -> unit
(* Goals can be not interesting, when they are trivial *)

val is_not_interesting : goal -> bool
val is_interesting : goal -> bool
(* query the "interesting" bit *)

val get_objective : goal -> objective
(* get the objective associated with a goal *)

(* Scheduling and proof *)
val next : objective -> goal list
(* For an objective, successive calls of [next] will return all goals
   associated to the objective, by chunks of size Gnat_config.parallel. [] is
   returned if no goals are left. One can add new goals to an objective at any
   time. *)

type status =
   | Proved
   | Not_Proved
   | Work_Left
   | Counter_Example
(* These are the possible statuses of an objective.
   [Proved] means that all goals of that objectives are proved.
   [Not_Proved] means that a proof attempt for a goal of the objective that
               cannot (or should not) be further simplified has failed.

   In both cases, there is no more work to do, and we can issue a message to
   the user.

   [Work_Left] means that we don't know yet whether the objective is proved or
               not, this means that all subgoals were proved up to now or if
               unproved could be further simplified, but there is some work
               left.
   [Counter_Example] means that the objective cannot be proved and the
               counterexample should be generated.
*)

val register_result : goal -> bool -> objective * status
(* Register the result of a prover for a given goal, and return the updated
 * status of the objective, as well as the objective itself *)

(* Auxiliary functions *)

val iter : (objective -> unit) -> unit
(* iterate over all objectives *)

val iter_leaf_goals : subp -> (goal -> unit) -> unit
(* iterate over all VCs of a subprogram. The callback will get an individual VC
   and the subp entity of the VC *)

val all_provers_tried : goal -> bool
(* check whether an existing valid proof attempt exists for the goal, for all
   requested provers *)

val objective_status : objective -> status
(* query the status of the objective *)

val get_num_goals : unit -> int
(* return the total number of goals *)

val get_num_goals_done : unit -> int
(* return the number of goals done *)

val init : unit -> unit
(* initialize the session, and return the session. The boolean is true when the
   session is new, otherwise "false" *)

val schedule_goal : cntexample : bool -> goal -> unit
(* schedule a goal for proof with default prover and
   default timeout. The function returns immediately.
   @param cntexample indicates whether the prover should be queried for
     a counterexample.
*)

val schedule_goal_with_prover :
  cntexample : bool -> goal -> Session.loaded_prover -> unit
(* schedule a goal for proof with given prover and
   default timeout. The function returns immediately.
   @param cntexample indicates whether the prover should be queried for
     a counterexample.
*)


val do_scheduled_jobs :
   (key Session.proof_attempt -> Session.proof_attempt_status -> unit) ->
  unit
(* run all the jobs that have been scheduled with [schedule_goal] *)

val save_session : unit -> unit
(* save the session; should be called on exit. *)

module GoalMap : Hashtbl.S with type key = goal
(* a map of goals *)

(* dealing with a main goal *)

val iter_subps : (subp -> unit) -> unit
(* iterate over all subprograms. *)

val init_subp_vcs : subp -> unit
(* init the vcs for a given subp *)

val clear : unit -> unit
(* delete all info from the database, except for the session tree itself *)

val matches_subp_filter : subp -> bool
(* check if the subprogram is filtered by command line option --limit-subp *)

module Save_VCs : sig
   (* Provide saving of VCs, traces *)

   val extract_stats : objective -> Gnat_report.stats

   val save_trace : goal -> (string * Gnat_loc.S.t)
   (* compute the trace from the goal and save it to a file; return the trace
      file name and the computed trace,
      ("", Gnat_loc.S.empty) if no trace was saved *)

   val vc_file : goal -> string
   (* get the file name for a given goal *)
end

val all_split_leaf_goals : unit -> unit
(* special-purpose function for "all_split" mode (see gnat_config.mli),
   where all split VCs are saved to disk, and no prover is called. *)

val clean_automatic_proofs : goal -> unit
(* deletes previous proof attempts of the selected provers for this goal *)

val goal_has_splits : goal -> bool

val session_proved_status : objective -> bool
(* check the proof status of an objective by looking at the verified/not
   verified status of its VCs in the session *)

val session_find_unproved_pa : objective -> key Session.proof_attempt option
(* find the first unproved proof attempt in a session. If counter examples are
 * activated, this will return a CE proof attempt, if any *)

val replay : unit -> unit
