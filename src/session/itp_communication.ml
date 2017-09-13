(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Information that the IDE may want to have *)
type prover = string
type transformation = string
type strategy = string


type node_ID = int
let root_node : node_ID = 0


type global_information =
    {
     provers         : (string * prover) list;
     transformations : transformation list;
     strategies      : (string * strategy) list;
     commands        : string list;
     (* hidden_provers       : string list; *)
     (* session_time_limit   : int; *)
     (* session_mem_limit    : int; *)
     (* session_nb_processes : int; *)
     (* session_cntexample   : bool; *)
     (* main_dir             : string *)
    }

type message_notification =
  | Proof_error           of node_ID * string
  | Transf_error          of node_ID * string * string * Loc.position * string * string
  (* Transf_error (nid, trans_with_arg, arg_opt, loc, error_msg, doc_of_trans *)
  | Strat_error           of node_ID * string
  | Replay_Info           of string
  | Query_Info            of node_ID * string
  | Query_Error           of node_ID * string
  | Help                  of string
  | Information           of string
  | Task_Monitor          of int * int * int
  | Parse_Or_Type_Error   of Loc.position * string
  | File_Saved            of string
  | Error                 of string
  | Open_File_Error       of string

type node_type =
  | NRoot
  | NFile
  | NTheory
  | NTransformation
  | NGoal
  | NProofAttempt

(* Used to give colors to the parts of the source code that corresponds to the
   following property in the current task. For example, the code corresponding
   to the goal of the task will have Goal_color in the source code. *)
type color =
  | Neg_premise_color
  | Premise_color
  | Goal_color

type update_info =
  | Proved of bool
  | Proof_status_change of
      Controller_itp.proof_attempt_status
      * bool   (* obsolete or not *)
      * Call_provers.resource_limit

type notification =
  | New_node     of node_ID * node_ID * node_type * string * bool
  (* Notification of creation of new_node:
     New_node (new_node, parent_node, node_type, name, detached). *)
  | Node_change  of node_ID * update_info
  (* inform that the data of the given node changed *)
  | Remove       of node_ID
  (* the given node was removed *)
  | Next_Unproven_Node_Id of node_ID * node_ID
  (* Next_Unproven_Node_Id (asked_id, next_unproved_id). Returns a node and the
     next unproven node from this node *)
  | Initialized  of global_information
  (* initial global data *)
  | Saved
  (* the session was saved on disk *)
  | Message      of message_notification
  (* an informative message, can be an error message *)
  | Dead         of string
  (* server exited *)
  | Task         of node_ID * string * (Loc.position * color) list
  (* the node_ID's task together with information that allows to color the
     source code corresponding to different part of the task (premise, goal,
     etc) *)
  | File_contents of string * string
  (* File_contents (filename, contents) *)

type ide_request =
  | Command_req             of node_ID * string
(*
  | Prove_req               of node_ID * prover * Call_provers.resource_limit
*)
  | Transform_req           of node_ID * transformation * string list
  | Strategy_req            of node_ID * strategy
  | Edit_req                of node_ID * prover
(*
  | Open_session_req        of string
 *)
  | Add_file_req            of string
  | Set_max_tasks_req       of int
  | Get_file_contents       of string
  | Get_task                of node_ID * bool * bool
  | Focus_req               of node_ID
  | Unfocus_req
  | Remove_subtree          of node_ID
  | Copy_paste              of node_ID * node_ID
  | Copy_detached           of node_ID
  | Save_file_req           of string * string
  | Get_first_unproven_node of node_ID
  | Mark_obsolete_req       of node_ID
  | Get_Session_Tree_req
  | Clean_req
  | Save_req
  | Reload_req
  | Replay_req
  | Exit_req
  | Interrupt_req

(* Return true if the request modify the session *)
let modify_session (r: ide_request) =
  match r with
  | Command_req _ (* | Prove_req _ *) | Transform_req _ | Strategy_req _
  | Add_file_req _ | Remove_subtree _ | Copy_paste _ | Copy_detached _
  | Replay_req | Clean_req | Mark_obsolete_req _ | Edit_req _ -> true

  (*| Open_session_req _ *)
  | Set_max_tasks_req _ | Get_file_contents _
  | Get_task _ | Save_file_req _ | Get_first_unproven_node _
  | Get_Session_Tree_req | Save_req | Reload_req | Exit_req
  | Interrupt_req | Focus_req _ | Unfocus_req -> false
