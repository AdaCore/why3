



(** {1 New Proof sessions ("Refectoire")} *)


(** {2 upper level structure of sessions}

   A [session] contains a collection of files, a [file] contains a
collection of theories, a [theory] contains a collection of goals. The
structure of goals remain abstract, each goal being identified by
unique identifiers of type [proofNodeId]

*)

type session

type proofNodeID

type theory

val theory_name : theory -> Ident.ident
val theory_goals : theory -> proofNodeID list

type file = private {
  file_name     : string;
  file_format   : string option;
  file_theories : theory list;
}

val get_files : session -> file Stdlib.Hstr.t



(** {2 Proof trees}

Each goal

*)



type proof_attempt = {
  prover              : Whyconf.prover;
  limit               : Call_provers.resource_limit;
  mutable proof_state : Call_provers.prover_result option;
  (* None means that the call was not done or never returned *)
  proof_obsolete      : bool;
  proof_script        : string option;  (* non empty for external ITP *)
}
type transID


type proof_parent = Trans of transID | Theory of theory

(* This is not needed
type tree = {
    tree_node_id : proofNodeID;
    tree_goal_name : string;
    tree_proof_attempts : proof_attempt list; (* proof attempts on this node *)
    tree_transformations : (transID * string * tree list) list;
                                (* transformations on this node *)
  }
(* a tree is a complete proof whenever at least one proof_attempf or
  one transformation proves the goal, where a transformation proves a
  goal when all subgoals have a complete proof.  In other word, the
  list of proof_attempt and transformation are "disjunctive" but the
  list of tree below a transformation is "conjunctive" *)
*)

(*
val get_tree : session -> proofNodeID -> tree
(** [get_tree s id] returns the proof tree of the goal identified by
    [id] *)
*)

val get_task : session -> proofNodeID -> Task.task

(* temp *)
(*
val get_node : session -> int -> proofNodeID
val get_trans : session -> int -> transID
*)

(* [print_proof_node s fmt t]: From definition of s, print on fmt the tree
   rooted at element t *)
val print_proof_node : session -> Format.formatter -> proofNodeID -> unit

(* [print_theory s fmt t]: From definition of s, print on fmt the theory t *)
val print_theory : session -> Format.formatter -> theory -> unit

(* [print_trans s fmt tn]: From definition of s, print on fmt the tree originating
   from transformation tn *)
val print_trans_node : session -> Format.formatter -> transID -> unit

val print_session : Format.formatter -> session -> unit

(* val get_proof_attempts : session -> proofNodeID -> proof_attempt Whyconf.Hprover.t *)
val get_transformations : session -> proofNodeID -> transID list
val get_proof_attempts : session -> proofNodeID -> proof_attempt list
val get_sub_tasks : session -> transID -> proofNodeID list

val get_transf_args : session -> transID -> string list
val get_transf_name : session -> transID -> string

val get_proof_name : session -> proofNodeID -> Ident.ident

val get_proof_parent : session -> proofNodeID -> proof_parent
val get_trans_parent : session -> transID -> proofNodeID

val empty_session : ?shape_version:int -> unit -> session

val add_file_section :
  session -> string -> (Theory.theory list) -> Env.fformat option ->
  session -> theory list -> unit
(** [add_file_section s fn ths old_s old_ths] adds a new 'file'
    section in session [s], named [fn], containing fresh theory
    subsections corresponding to theories [ths]. The tasks of each
    theory nodes generated are computed using [Task.split_theory]. For
    each theory whose name is identical to one theory of old_ths, it
    is attempted to associate the old goals, proof_attempts and transformations
    to the goals of the new theory *)

val graft_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  timelimit:int -> unit
(** [graft_proof_attempt s id pr t] adds a proof attempt with prover
    [pr] and timelimit [t] in the session [s] as a child of the task
    [id]. If there already a proof attempt with the same prover,
    it updates it with the new timelimit. *)

val update_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  Call_provers.prover_result -> unit
(** [update_proof_attempt s id pr st] update the status of the
    corresponding proof attempt with [st]. *)

val graft_transf : session -> proofNodeID -> string -> string list ->
   Task.task list -> transID
(** [graft_transf s id name l tl] adds the transformation [name] as a
    child of the task [id] of the session [s]. [l] is the list of
    arguments of the transformation, and [tl] is the list of subtasks.
 *)

val remove_proof_attempt : session -> proofNodeID -> Whyconf.prover -> unit
(** [remove_proof_attempt s id pr] removes the proof attempt from the
    prover [pr] from the proof node [id] of the session [s] *)

val remove_transformation : session -> transID -> unit
(** [remove_transformation s id] removes the transformation [id]
    from the session [s] *)

val save_session : string -> session -> unit
(** [save_session f s] Save the session [s] in file [f] *)

val load_session : string -> session
(** [load_session f] load a session from a file [f]; all the tasks are
    initialised to None *)
