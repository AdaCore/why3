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

(* Information that the IDE may want to have *)
type transformation = (string * string)
type strategy = string


type node_ID = int
let root_node : node_ID = 0

let is_root n = n = root_node

type global_information =
  {
    provers         : (string * string * string) list;
    (* (shortcut, human readable name, parseable name) *)
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
  | Transf_error          of bool * node_ID * string * string * Loc.position * string * string
  (* Transf_error (nid, trans_with_arg, arg_opt, loc, error_msg, doc_of_trans *)
  | Strat_error           of node_ID * string
  | Replay_Info           of string
  | Query_Info            of node_ID * string
  | Query_Error           of node_ID * string
  | Information           of string
  | Task_Monitor          of int * int * int
  | Parse_Or_Type_Error   of Loc.position * Loc.position * string
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
  | Error_color
  | Error_line_color
  | Error_font_color
  | Search_color

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
  | Saving_needed of bool
  (* the session needs saving when argument is true *)
  | Saved
  (* the session was saved on disk *)
  | Message      of message_notification
  (* an informative message, can be an error message *)
  | Dead         of string
  (* server exited *)
  | Task         of node_ID * string * (Loc.position * color) list * Loc.position option * Env.fformat
  (* [n, s, list_loc, goal_loc, lang] with
     - [n] the node_ID's task,
     - [s] the task to be displayed
     - [list_loc] a list of location to color the source,
     - [goal_loc] the location of the goal,
     - [lang] the language to load in Why3ide for syntax coloring
  *)
  | File_contents of string * string * Env.fformat * bool
  (* File_contents (filename, contents, format, read_only) *)
  | Source_and_ce of string * (Loc.position * color) list * Loc.position option * Env.fformat
  (* Source interleaved with counterexamples: contents, list color loc,
     loc of the goal, format of the source *)
  | Ident_notif_loc of Loc.position
  (* Answer the position where an ident is defined *)

type next_unproved_node_strat =
  | Prev
  | Next
  | Clever

type ide_request =
  | Command_req             of node_ID * string
  | Add_file_req            of string
  | Set_config_param        of string * int
  | Set_prover_policy       of Whyconf.prover * Whyconf.prover_upgrade_policy
  | Get_file_contents       of string
  | Get_task                of node_ID * bool * bool
  | Remove_subtree          of node_ID
  | Copy_paste              of node_ID * node_ID
  | Save_file_req           of string * string
  | Get_first_unproven_node of next_unproved_node_strat * node_ID
  | Find_ident_req          of Loc.position
  | Unfocus_req
  | Save_req
  | Reload_req
  | Check_need_saving_req
  | Exit_req
  | Interrupt_req
  | Reset_proofs_req
  | Get_global_infos


(* Debugging functions *)

open Format

let print_request fmt r =
  match r with
  | Command_req (_nid, s)           -> fprintf fmt "command \"%s\"" s
  | Add_file_req f                  -> fprintf fmt "open file %s" f
  | Set_config_param(s,i)           -> fprintf fmt "set config param %s %i" s i
  | Set_prover_policy(p1,p2)        ->
     fprintf fmt "set prover policy %a -> %a" Whyconf.print_prover p1
             Whyconf.print_prover_upgrade_policy p2
  | Get_file_contents _f            -> fprintf fmt "get file contents"
  | Get_first_unproven_node (_,_nid)-> fprintf fmt "get first unproven node"
  | Find_ident_req _                -> fprintf fmt "find ident"
  | Get_task(nid,b,loc)             -> fprintf fmt "get task(%d,%b,%b)" nid b loc
  | Remove_subtree _nid             -> fprintf fmt "remove subtree"
  | Copy_paste _                    -> fprintf fmt "copy paste"
  | Save_file_req _                 -> fprintf fmt "save file"
  | Unfocus_req                     -> fprintf fmt "unfocus"
  | Save_req                        -> fprintf fmt "save"
  | Reload_req                      -> fprintf fmt "reload"
  | Check_need_saving_req           -> fprintf fmt "check need saving"
  | Exit_req                        -> fprintf fmt "exit"
  | Interrupt_req                   -> fprintf fmt "interrupt"
  | Reset_proofs_req                -> fprintf fmt "reset proofs"
  | Get_global_infos                -> fprintf fmt "get_global_infos"

let print_msg fmt m =
  match m with
  | Proof_error (_ids, s)                        -> fprintf fmt "proof error %s" s
  | Transf_error (b, _ids, _tr, _args, _loc, s, _d) ->
      fprintf fmt "transf error (is fatal = %b) %s" b s
  | Strat_error (_ids, s)                        -> fprintf fmt "start error %s" s
  | Replay_Info s                                -> fprintf fmt "replay info %s" s
  | Query_Info (_ids, s)                         -> fprintf fmt "query info %s" s
  | Query_Error (_ids, s)                        -> fprintf fmt "query error %s" s
  | Information s                                -> fprintf fmt "info %s" s
  | Task_Monitor _                               -> fprintf fmt "task montor"
  | Parse_Or_Type_Error (_, _, s)                -> fprintf fmt "parse_or_type_error:\n %s" s
  | File_Saved s                                 -> fprintf fmt "file saved %s" s
  | Error s                                      -> fprintf fmt "%s" s
  | Open_File_Error s                            -> fprintf fmt "%s" s

(* TODO ad hoc printing. Should reuse print_loc. *)
let print_loc fmt (loc: Loc.position) =
  let (f,l,b,e) = Loc.get loc in
   fprintf fmt "File \"%s\", line %d, characters %d-%d" f l b e

let _print_list_loc fmt l =
  Pp.print_list
    (fun _fmt () -> ())
    (fun fmt (loc, _c) -> Format.fprintf fmt "(%a, color)" print_loc loc)
    fmt l

let print_notify fmt n =
  match n with
  | Reset_whole_tree -> fprintf fmt "reset whole tree"
  | Node_change (ni, nf) ->
      begin
        match nf with
        | Proved b -> fprintf fmt "node change %d: proved=%b" ni b
        | Name_change n -> fprintf fmt "node change %d: renamed to '%s'" ni n
        | Proof_status_change(st,b,_lim) ->
           fprintf fmt "node change %d Proof_status_change res=%a obsolete=%b limits=<TODO>"
                   ni Controller_itp.print_status st b
      end
  | New_node (ni, pni, _nt,  _nf, _d) -> fprintf fmt "new node = %d, parent = %d" ni pni
  | Remove _ni                        -> fprintf fmt "remove"
  | Next_Unproven_Node_Id (ni, nj)    -> fprintf fmt "next unproven node_id from %d is %d" ni nj
  | Initialized _gi                   -> fprintf fmt "initialized"
  | Saving_needed b                   -> fprintf fmt "saving needed=%b" b
  | Saved                             -> fprintf fmt "saved"
  | Message msg                       ->
      print_msg fmt msg
  | Dead s                            -> fprintf fmt "dead :%s" s
  | File_contents (f, _s, _, _)       -> fprintf fmt "file contents %s" f
  | Source_and_ce (_, _list_loc, _gl, _) -> fprintf fmt "source and ce"
  | Task (ni, _s, list_loc, g_loc, _lang) ->
      fprintf fmt "task for node_ID %d which contains a list of %d locations. Goal_location = %a"
        ni (List.length list_loc)
        (Pp.print_option print_loc) g_loc (* print_list_loc list_loc *)
  | Ident_notif_loc loc               ->
      fprintf fmt "ident notification %a" Pretty.print_loc loc
