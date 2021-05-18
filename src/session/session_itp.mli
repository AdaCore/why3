(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(** Proof sessions *)



(** {2 upper level structure of sessions}

   A [session] contains a collection of files, a [file] contains a
collection of theories, a [theory] contains a collection of goals. The
structure of goals remain abstract, each goal being identified by
unique identifiers of type [proofNodeId]

*)

type session
type file
type theory
type proofNodeID
val print_proofNodeID : Format.formatter -> proofNodeID -> unit
type transID
type proofAttemptID
val print_proofAttemptID : Format.formatter -> proofAttemptID -> unit
type fileID

module Hfile: Exthtbl.S with type key = fileID
module Hpn: Exthtbl.S with type key = proofNodeID
module Htn: Exthtbl.S with type key = transID
module Hpan: Exthtbl.S with type key = proofAttemptID

(* Any proof node of the tree *)
type any =
  | AFile of file
  | ATh of theory
  | ATn of transID
  | APn of proofNodeID
  | APa of proofAttemptID

val fprintf_any: Format.formatter -> any -> unit

type notifier = any -> unit


(** Session *)

(* Get all the files in the session *)
val get_files : session -> file Hfile.t
(* Get a single file in the session using its name *)
(* val get_file: session -> string -> file *)
(* Get directory containing the session *)
val get_dir : session -> string

(** File *)
val file_id : file -> fileID
val file_path : file -> Sysutil.file_path
val file_format : file -> string
val file_theories : file -> theory list
val system_path : session -> file -> string
(** the system-dependent absolute path associated to that file *)

(** Theory *)
val theory_name : theory -> Ident.ident
val theory_goals : theory -> proofNodeID list
val theory_parent : session -> theory -> file

type proof_attempt_node =
  private {
      parent                 : proofNodeID;
      mutable prover         : Whyconf.prover;
      limit                  : Call_provers.resource_limit;
      mutable proof_state    : Call_provers.prover_result option;
      (* None means that there is a prover call in progress *)
      mutable proof_obsolete : bool;
      mutable proof_script   : Sysutil.file_path option;  (* non empty for external ITP *)
    }

val set_proof_script : proof_attempt_node -> Sysutil.file_path -> unit

(* [is_below s a b] true if a is below b in the session tree *)
val is_below: session -> any -> any -> bool

type proof_parent = Trans of transID | Theory of theory


val get_task : session -> proofNodeID -> Task.task
val get_task_name_table : session -> proofNodeID -> Task.task * Trans.naming_table

val get_transformations : session -> proofNodeID -> transID list
val get_proof_attempt_ids :
  session -> proofNodeID -> proofAttemptID Whyconf.Hprover.t

exception BadID

val get_proof_attempt_node : session -> proofAttemptID -> proof_attempt_node
val get_proof_attempt_parent : session -> proofAttemptID -> proofNodeID
val get_proof_attempts : session -> proofNodeID -> proof_attempt_node list
val get_sub_tasks : session -> transID -> proofNodeID list

val get_transf_args : session -> transID -> string list
val get_transf_name : session -> transID -> string

val get_proof_name : session -> proofNodeID -> Ident.ident
val get_proof_expl : session -> proofNodeID -> string

val get_proof_parent : session -> proofNodeID -> proof_parent
val get_trans_parent : session -> transID -> proofNodeID

val find_th : session -> proofNodeID -> theory

val get_any_parent: session -> any -> any option

(* Answers true if a node is in a detached subtree *)
val is_detached: session -> any -> bool

(* get the parent theory/file of a proof node *)
val get_encapsulating_theory: session -> any -> theory
val get_encapsulating_file: session -> any -> file

(* Check if a transformation already exists *)
val check_if_already_exists:
    session -> proofNodeID -> string -> string list -> bool

(* true if the exception transformation is fatal (ie: caused by a bug in the
   code of the transformation) *)
val is_fatal: exn -> bool

(** {2 iterators on sessions} *)

val goal_iter_proof_attempt:
    session -> (proofAttemptID -> proof_attempt_node -> unit) -> proofNodeID -> unit

val theory_iter_proof_attempt:
    session -> (proofAttemptID -> proof_attempt_node -> unit) -> theory -> unit

val file_iter_proof_attempt:
    session -> (proofAttemptID -> proof_attempt_node -> unit) -> file -> unit

val any_iter_proof_attempt:
    session -> (proofAttemptID -> proof_attempt_node -> unit) -> any -> unit

val session_iter_proof_attempt:
    (proofAttemptID -> proof_attempt_node -> unit) -> session -> unit

val fold_all_any: session -> ('a -> any -> 'a) -> 'a -> any -> 'a
(** [fold_all_any s f acc any] folds on all the subnodes of any *)

val fold_all_session: session -> ('a -> any -> 'a) -> 'a -> 'a
(** [fold_all_session s f acc] folds on the whole session *)


(** {2 session operations} *)


val empty_session :
  ?sum_shape_version:Termcode.sum_shape_version -> ?from:session ->
  string -> session
(** create an empty_session in the directory specified by the
   argument. If [sum_shape_version] is present it will record it for
   the generated session, otherwise the current version is taken from
   module [Termcode].  If [from] is present, the provers, sum-shape
   version and global shapes are taken from it.  It is forbidden to
   pass both [sum_shape_version] and [from] arguments.  *)

val add_file_section :
  session -> string -> file_is_detached:bool -> Theory.theory list->
  Env.fformat -> file
(** [add_file_section s fn ths] adds a new
    'file' section in session [s], named [fn], containing fresh theory
    subsections corresponding to theories [ths]. The tasks of each
    theory nodes generated are computed using [Task.split_theory].

    Note that this function does not read anything from the file
    system. The file name [fn] is taken as is

 *)

val read_file :
  Env.env -> ?format:Env.fformat -> string -> (Theory.theory list) * Env.fformat
(* [read_file env ~format fn] parses the source file [fn], types it
   and extract its theories. A parse error or a typing error is
   signaled with exceptions.
   The second returned element is the format of the file that was read.
*)

val merge_files :
  Env.env -> session -> session -> exn list * bool * bool
(** [merge_files env ses old_ses] merges the file sections
    of session [s] with file sections of the same name in old session
    [old_ses]. Recursively, for each theory whose name is identical to
    old theories, it is attempted to associate the old goals,
    proof_attempts and transformations to the goals of the new theory.
    Returns a triple [(e,o,d)] such that [e] is the list of parsing or
    typing errors found, [o] is true when obsolete proof attempts
    where found and [d] is true if detached theories, goals or
    transformations were found.  *)

val graft_proof_attempt : ?file:Sysutil.file_path -> session -> proofNodeID ->
  Whyconf.prover -> limit:Call_provers.resource_limit -> proofAttemptID
(** [graft_proof_attempt s id pr file l] adds a proof attempt with prover
    [pr] and limits [l] in the session [s] as a child of the task
    [id]. If there already a proof attempt with the same prover, it
    updates it with the limits. It returns the id of the
    generated proof attempt.
    For manual proofs, it has the same behaviour except that it adds a
    proof_script field equal to [file].
*)

exception NoProgress
val apply_trans_to_goal :
  allow_no_effect:bool -> session -> Env.env -> string -> string list ->
  proofNodeID -> Task.task list
(** [apply_trans_to_goal s env tr args id] applies the transformation
  [tr] with arguments [args] to the goal [id], and returns the
  subtasks.  raises [NoProgress] if [allow_no_effect] is false and [tr]
  returns the task unchanged *)

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

val mark_obsolete: session -> proofAttemptID -> unit
(** [mark_obsolete s id] marks [id] as obsolete in [s] *)

val save_session : session -> unit
(** [save_session s] Save the session [s] *)

val load_session : string -> session
(** [load_session dir] load a session in directory [dir]; all the
    tasks are initialised to None

    raises [SessionFileError msg] if the database file cannot be read
    correctly.

    raises [ShapesFileError msg] if the database extra file for shapes
    cannot be read.
 *)

(** {2 remove} *)

exception RemoveError

val remove_subtree: notification:notifier -> removed:notifier ->
                    session -> any -> unit
(** [remove_subtree s a ~removed ~notification] remove the subtree
    originating from node [a] in session [s]. the notifier [removed] is
    called on each removed node, and notifier [notification] on nodes
    whose proved state changes.

    raises [RemoveError] when removal is forbidden, e.g. when called on
    a file, a theory or a goal that is not detached
 *)

(** {2 proved status} *)

val pa_proved : session -> proofAttemptID -> bool
val th_proved : session -> theory -> bool
val pn_proved : session -> proofNodeID -> bool
val tn_proved : session -> transID -> bool
val file_proved : session -> file -> bool
val any_proved : session -> any -> bool

val update_goal_node : notifier -> session -> proofNodeID -> unit
(** updates the proved status of the given goal node. If necessary,
    propagates the update to ancestors. [notifier] is called on all
    nodes whose status changes. *)

val update_trans_node : notifier -> session -> transID -> unit
(** updates the proved status of the given transformation node. If
    necessary, propagates the update to ancestors. [notifier] is
    called on all nodes whose status changes *)

val update_proof_attempt : ?obsolete:bool -> notifier -> session -> proofNodeID ->
  Whyconf.prover -> Call_provers.prover_result -> unit
(** [update_proof_attempt ?obsolete s id pr st] update the status of the
    corresponding proof attempt with [st].
    If [obsolete] is set to true, it marks the proof_attempt obsolete
    directly (useful for interactive prover).
*)

val change_prover : notifier -> session -> proofNodeID -> Whyconf.prover -> Whyconf.prover -> unit
(** [change_prover s id opr npr] changes the prover of the proof
   attempt using prover [opr] by the new prover [npr]. Proof attempt
   status is set to obsolete.
 *)

(** Extra session update operations *)

val find_file_from_path: session -> Sysutil.file_path -> file
(** raise [Not_found] of path does not appear in session *)

val rename_file: session -> string -> string -> Sysutil.file_path * Sysutil.file_path
(** [rename_file s from_file to_file] renames the
    file section in session [s] named [from_file] into [to_file]
    @return the paths relative to the session dir

    Beware that this function does not have any effect on the user's
    file system: if the considered files corresponds the real files,
    they must be renamed independently. See for example the use in
    [why3session/why3session_update].
  *)
