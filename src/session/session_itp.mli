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
    (int * string * int * (int * string * int * tree list) list)

val get_tree : session -> (string * (string * tree list) list) list

(* Note for big brother Andrei: grafting is the opposite of pruning *)

val empty_session : ?shape_version:int -> string -> session

val add_file_section :
  session -> string -> ?format:string -> Theory.theory list -> unit
(** [add_file_section s fn ths] adds a new 'file' section in session
    [s], named [fn], containing fresh theory subsections corresponding
    to theories [ths]. The tasks of each theory nodes generated are
    computed using [Task.split_theory] *)

val graft_proof_attempt : session -> proofNodeID -> proof_attempt -> unit
(** [graft_proof_attempt s id pa] adds the proof attempt [pa] as a
    child of the task [id] of the session [s]. *)

val graft_transf : session -> proofNodeID -> string -> trans_arg list ->
  Task.task list -> unit
(** [graft_transf s id name l tl] adds the transformation [name] as a
    child of the task [id] of the session [s]. [l] is the list of
    argument of the transformation; [tl] is the resulting list of
    tasks *)


(*
val remove_proof_attempt : session -> proofNodeID -> Whyconf.prover -> unit
(** [remove_proof_attempt s id pr] removes the proof attempt from the
    prover [pr] from the proof node [id] of the session [s] *)

val remove_transformation : session -> transID -> unit
(** [remove_transformation s id] removes the transformation [id]
    from the session [s] *)

(*
val save_session : string -> session -> unit
 *)
(** [save_session f s] Save the session [s] in file [f] *)
 *)


val load_session : string -> session * bool
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
