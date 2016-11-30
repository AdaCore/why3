open Call_provers

type prover = string
type transformation = string
type strategy = string
type infos =
    {hidden_provers : string list;
     session_time_limit : int;
     session_mem_limit : int;
     session_nb_processes : int;
     session_cntexample : bool;
     main_dir : string}

(* TODO:
   Size of the name can be proportionnal to the size of the tree.
   Maybe, we should find an other solution *)
type node_ID = string
type pos_ID = string
val root_node : node_ID

(* --------------------------- types to be expanded if needed --------------------------------- *)

type node_type = Root | File | Theory | Transformation | Goal | ProofAttempt of bool

type node_info = { proved : bool; (* TODO: add more *)
                   name   : string }

(* todo, separate what's updatable from the rest in types *)

(* pos_ID is the suffix of node_ID: its position in its brothers list *)
type session_tree =
  | Node of node_ID * pos_ID * node_type * node_info * session_tree list

type error_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string
  | Strat_error  of node_ID * string

type notification =
  | Node_change    of node_ID * node_info
  (* inform that the data of the given node changed *)
  | New_subtree    of node_ID * session_tree
  (* the given node has a new child whose contents is the given tree *)
  | Remove         of node_ID
  (* the given node was removed *)
  | Initialized    of infos * prover list * transformation list * strategy list
  (* initial global data *)
  | Saved
  (* the session was saved on disk *)
  | Session_Tree   of session_tree
  (* the full session tree is sent *)
  | Error          of error_notification
  (* an error occured *)
  | Message        of string
  (* an informative message *)

type request_type =
  | Command   of string
  | Prove     of prover * resource_limit
  | Transform of transformation * string list
  | Strategy  of strategy
  | Open      of string
  | Get_Session_Tree
  | Save
  | Reload
  | Replay
  | Exit

type ide_request = request_type * node_ID

(* The server part of the protocol *)
module type Protocol = sig

  val get_requests : unit -> ide_request list
  val notify : notification -> unit

end

module Make (S:Controller_itp.Scheduler) (P:Protocol) : sig

  val get_config: unit -> Whyconf.config

  (* Nothing ! *)

end
