open Call_provers

type prover = string
type transformation = string
type strategy = string

type node_ID = int
val root_node : node_ID

(* --------------------------- types to be expanded if needed --------------------------------- *)

type node_type =
  | NRoot
  | NFile
  | NTheory
  | NTransformation
  | NGoal
  | NProofAttempt of Call_provers.prover_answer option * bool

type node_info = { proved : bool; (* TODO: add more *)
                   name   : string }

(* Global information known when server process has started and that can be
   shared with the IDE through communication *)
type global_information =
    {
     provers         : prover list;
     transformations : transformation list;
     strategies      : strategy list;
     commands        : string list;
     (* hidden_provers       : string list; *)
     (* session_time_limit   : int; *)
     (* session_mem_limit    : int; *)
     (* session_nb_processes : int; *)
     (* session_cntexample   : bool; *)
     (* main_dir             : string *)
    }

type message_notification =
  | Proof_error  of node_ID * string
  | Transf_error of node_ID * string
  | Strat_error  of node_ID * string
  | Replay_Info  of string
  | Query_Info   of node_ID * string
  | Query_Error  of node_ID * string
  | Help         of string
  (* General information *)
  | Information  of string
  (* Number of task scheduled, running, etc *)
  | Task_Monitor of int * int * int
  (* An error happened that could not be identified in server *)
  | Error        of string

type notification =
  | Node_change  of node_ID * node_info
  (* inform that the data of the given node changed *)
  | New_node     of node_ID * node_ID * node_type * node_info
  (* Notification of creation of new_node:
     New_node (new_node, parent_node, new_node_type, new_node_content). *)
  | Remove       of node_ID
  (* the given node was removed *)
  | Initialized  of global_information
  (* initial global data *)
  | Saved
  (* the session was saved on disk *)
  | Message      of message_notification
  (* an informative message, can be an error message *)
  | Dead         of string
  (* server exited *)
  | Proof_update of node_ID * Controller_itp.proof_attempt_status
  (* update proof attempt *)
  | Task         of node_ID * string
  (* te node_ID's task *)

type request_type =
  | Command_req       of string
  | Prove_req         of prover * resource_limit
  | Transform_req     of transformation * string list
  | Strategy_req      of strategy
  | Open_req          of string
  | Set_max_tasks_req of int
  | Get_task
  | Get_Session_Tree_req
  | Save_req
  | Reload_req
  | Replay_req
  | Exit_req

val print_request: Format.formatter -> request_type -> unit

(* TODO: change to request_type * node_ID list ? *)
type ide_request = request_type * node_ID

(* The server part of the protocol *)
module type Protocol = sig

  val get_requests : unit -> ide_request list
  val notify : notification -> unit

end

module Make (S:Controller_itp.Scheduler) (P:Protocol) : sig

  val get_configs: unit -> Whyconf.config * Whyconf.config

  (* Nothing ! *)

end
