type session
type transID
type proofNodeID
type proof_attempt
type trans_arg

(* New Proof sessions ("Refectoire") *)

(* note: la fonction register des transformations doit permettre de
   declarer les types des arguments

   type trans_arg_type = TTint | TTstring | TTterm | TTty | TTtysymbol
   | TTlsymbol | TTprsymbol

*)

type tree =
    Tree of
      (proofNodeID * string
       * proof_attempt list (* proof attempts in this node *)
       * (transID * string * tree list) list) (* transformation in this node *)

val get_theories : session -> (string * (string * proofNodeID list) list) list
(** [get_theories s] returns a list of pairs [name,l] where [name] is a
    file name and [l] is a list of pairs [thnmae,l'] where [thname] is
    a theory name and [l'] is the list of goal ids *)

val get_tree : session -> proofNodeID -> tree
(** [get_tree s id] returns the proof tree of the goal identified by
    [id] *)

(* temp *)
val get_node : session -> int -> proofNodeID
val get_trans : session -> int -> transID
val print_tree : session -> Format.formatter -> tree -> unit
val print_session : session -> unit

(* val get_proof_attempts : session -> proofNodeID -> proof_attempt Whyconf.Hprover.t *)
val get_transformations : session -> proofNodeID -> transID list
val get_sub_tasks : session -> transID -> proofNodeID list

(* Note for big brother Andrei: grafting is the opposite of pruning *)

val empty_session : ?shape_version:int -> unit -> session

val add_file_section :
  session -> string -> (Theory.theory list) -> Env.fformat option -> unit
(** [add_file_section s fn ths] adds a new 'file' section in session
    [s], named [fn], containing fresh theory subsections corresponding
    to theories [ths]. The tasks of each theory nodes generated are
    computed using [Task.split_theory] *)

val graft_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  timelimit:int -> unit
(** [graft_proof_attempt s id pr t] adds a proof attempt with prover
    [pr] and timelimit [t] in the session [s] as a child of the task
    [id]. If there allready a proof attempt with the same prover,
    it updates it with the new timelimit. *)

val update_proof_attempt : session -> proofNodeID -> Whyconf.prover ->
  Call_provers.prover_result option -> unit
(** [update_proof_attempt s id pr st] update the status of the
    corresponding proof attempt with [st]. *)

val graft_transf : session -> proofNodeID -> string -> trans_arg list ->
   transID
(** [graft_transf s id name l] adds the transformation [name] as a
    child of the task [id] of the session [s]. [l] is the list of
    argument of the transformation. The subtasks are initialized to
    the empty list *)

val set_transf_tasks : session -> transID -> Task.task list -> unit
(** [set_transf_tasks s id tl] sets the tasks of the transformation node
    [id] to [tl] *)

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


(*

  couche au-dessus: "scheduler" cad modifications asynchrones de la
  session

   - gere une file de travaux de modifications a faire

   - recupere les resultats de travaux , et les applique s'ils sont
     encore valides
*)
(*
type theory =
  {
    goals : sequence of task
  }

type file =
  {
    theories = sequence of theories
  }

type session =
  {
    session_files : set of files
  }
 *)
