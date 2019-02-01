(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(* Name and description *)
type transformation = (string * string)
type strategy = string

type node_ID = int
val root_node : node_ID

val is_root : node_ID -> bool

(* --------------------------- types to be expanded if needed --------------------------------- *)

(** Global information known when server process has started and that can be
   shared with the IDE through communication *)
type global_information =
  {
    provers         : (string * string * string) list;
    (* (shortcut, human readable name, parseable name) *)
    transformations : transformation list;
    strategies      : (string * strategy) list;
    commands        : string list
                             (* hidden_provers       : string list; *)
                             (* session_time_limit   : int; *)
                             (* session_mem_limit    : int; *)
                             (* session_nb_processes : int; *)
                             (* session_cntexample   : bool; *)
                             (* main_dir             : string *)
  }

type message_notification =
  | Proof_error           of node_ID * string
  | Transf_error          of bool * node_ID * string * string * Loc.position * string * string
  (** Transf_error (is_fatal, nid, trans_with_arg, arg_opt, loc, error_msg, doc_of_transf *)
  | Strat_error           of node_ID * string
  | Replay_Info           of string
  | Query_Info            of node_ID * string
  | Query_Error           of node_ID * string
  (** General information *)
  | Information           of string
  (** Number of task scheduled, running, etc *)
  | Task_Monitor          of int * int * int
  (** A file was read or reloaded and now contains a parsing or typing error.
     second loc is relative to the session file *)
  | Parse_Or_Type_Error   of Loc.position * Loc.position * string
  (** [File_Saved f] f was saved *)
  | File_Saved            of string
  (** An error happened that could not be identified in server *)
  | Error                 of string
  | Open_File_Error       of string

type node_type =
  | NRoot
  | NFile
  | NTheory
  | NTransformation
  | NGoal
  | NProofAttempt

(** Used to give colors to the parts of the source code that corresponds to the
   following property in the current task. For example, the code corresponding
   to the goal of the task will have Goal_color in the source code. *)
type color =
  | Neg_premise_color
  | Premise_color
  | Goal_color
  | Error_color
  | Error_line_color
  | Error_font_color

type update_info =
  | Proved of bool
  | Name_change of string
  | Proof_status_change of
      Controller_itp.proof_attempt_status
      * bool   (* obsolete or not *)
      * Call_provers.resource_limit

type notification =
  | Reset_whole_tree
  | New_node     of node_ID * node_ID * node_type * string * bool
  (** Notification of creation of new_node:
     New_node (new_node, parent_node, node_type, name, detached). *)
  | Node_change  of node_ID * update_info
  (** inform that the data of the given node changed *)
  | Remove       of node_ID
  (** the given node was removed *)
  | Next_Unproven_Node_Id of node_ID * node_ID
  (** Next_Unproven_Node_Id (asked_id, next_unproved_id). Returns a node and the
     next unproven node from this node *)
  | Initialized  of global_information
  (** initial global data *)
  | Saving_needed of bool
  (** the session needs saving when argument is true *)
  | Saved
  (** the session was just saved on disk *)
  | Message      of message_notification
  (** an informative message, can be an error message *)
  | Dead         of string
  (** server exited *)
  | Task         of node_ID * string * (Loc.position * color) list
  (** the node_ID's task together with information that allows to color the
     source code corresponding to different part of the task (premise, goal,
     etc) *)
  | File_contents of string * string
  (** File_contents (filename, contents) *)
  | Source_and_ce of string * (Loc.position * color) list
  (** Source interleaved with counterexamples: contents and list color loc *)

type ide_request =
  | Command_req             of node_ID * string
  (* executes the given command on the given node. command is
     interpreted by Server_utils.interp. This includes calling
     provers, applying transformations, stategies.  *)
  | Add_file_req            of string
  | Set_config_param        of string * int
  | Set_prover_policy       of Whyconf.prover * Whyconf.prover_upgrade_policy
  | Get_file_contents       of string
  | Get_task                of node_ID * bool * bool
  (** [Get_task(id,b,loc)] requests for the text of the task in node
      [id].  When [b] is true then the
      full context is show.  When [loc] is false the locations are not
      returned *)
  | Remove_subtree          of node_ID
  | Copy_paste              of node_ID * node_ID
  | Save_file_req           of string * string
  (** [Save_file_req(filename, content_of_file)] saves the file *)
  | Get_first_unproven_node of node_ID
  | Unfocus_req
  | Save_req
  | Reload_req
  | Check_need_saving_req
  | Exit_req
  | Interrupt_req
  | Get_global_infos


val print_request: Format.formatter -> ide_request -> unit
val print_msg: Format.formatter -> message_notification -> unit
val print_notify: Format.formatter -> notification -> unit
