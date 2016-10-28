



(** {1 New Proof sessions ("Refectoire")} *)


(** {2 upper level structure of sessions}

   A [session] contains a collection of files, a [file] contains a
collection of theories, a [theory] contains a collection of goals. The
structure of goals remain abstract, each goal being identified by
unique identifiers of type [proofNodeId]

*)

type session

type proofNodeID
val print_proofNodeID : Format.formatter -> proofNodeID -> unit

type transID

module Hpn: Exthtbl.S with type key = proofNodeID
module Htn: Exthtbl.S with type key = transID

val init_Hpn: session ->'a Hpn.t -> 'a -> unit
val init_Htn: session ->'a Htn.t -> 'a -> unit

type theory

val theory_name : theory -> Ident.ident
val theory_goals : theory -> proofNodeID list
val theory_detached_goals : theory -> proofNodeID list

type file = private {
  file_name              : string;
  file_format            : string option;
  file_theories          : theory list;
  file_detached_theories : theory list;
}

val get_files : session -> file Stdlib.Hstr.t
val get_dir : session -> string
val get_shape_version : session -> int


type proof_attempt = {
  prover              : Whyconf.prover;
  limit               : Call_provers.resource_limit;
  mutable proof_state : Call_provers.prover_result option;
  (* None means that the call was not done or never returned *)
  mutable proof_obsolete      : bool;
  proof_script        : string option;  (* non empty for external ITP *)
}


type proof_parent = Trans of transID | Theory of theory

val get_task : session -> proofNodeID -> Task.task

val get_transformations : session -> proofNodeID -> transID list
val get_proof_attempts : session -> proofNodeID -> proof_attempt list
val get_sub_tasks : session -> transID -> proofNodeID list
val get_detached_sub_tasks : session -> transID -> proofNodeID list

val get_transf_args : session -> transID -> string list
val get_transf_name : session -> transID -> string

val get_proof_name : session -> proofNodeID -> Ident.ident

val get_proof_parent : session -> proofNodeID -> proof_parent
val get_trans_parent : session -> transID -> proofNodeID

val empty_session : ?shape_version:int -> string -> session
(** create an empty_session in the directory specified by the
    argument *)

val add_file_section :
  use_shapes:bool -> ?merge:session*theory list*Env.env -> session ->
  string -> (Theory.theory list) -> Env.fformat option -> unit
(** [add_file_section ~merge:(old_s,old_ths,env) s fn ths] adds a new
    'file' section in session [s], named [fn], containing fresh theory
    subsections corresponding to theories [ths]. The tasks of each
    theory nodes generated are computed using [Task.split_theory]. For
    each theory whose name is identical to one theory of old_ths, it
    is attempted to associate the old goals, proof_attempts and
    transformations to the goals of the new theory *)

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

val save_session : session -> unit
(** [save_session s] Save the session [s] *)

val load_session : string -> session * bool
(** [load_session dir] load a session in directory [dir]; all the
    tasks are initialised to None

    The returned boolean is set when there was shapes read from disk.

    raises [SessionFileError msg] if the database file cannot be read
    correctly.

    raises [ShapesFileError msg] if the database extra file for shapes
    cannot be read.
 *)
