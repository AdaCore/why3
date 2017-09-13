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

open Itp_communication
open Controller_itp
open Call_provers
open Json_base

(* TODO match exceptions and complete some cases *)

let convert_prover_to_json (p: Whyconf.prover) =
  Record (convert_record
    ["prover_name", String p.Whyconf.prover_name;
     "prover_version", String p.Whyconf.prover_version;
     "prover_altern", String p.Whyconf.prover_altern])

let convert_infos (i: global_information) =
  let convert_prover (s,p) =
    Record (convert_record ["prover_shorcut", String s;
                            "prover_name", String p])
  in
  let convert_strategy (s,p) =
    Record (convert_record ["strategy_shorcut", String s;
                            "strategy_name", String p])
  in
  Record (convert_record
    ["provers", List (List.map convert_prover i.provers);
     "transformations", List (List.map (fun x -> String x) i.transformations);
     "strategies", List (List.map convert_strategy i.strategies);
     "commands", List (List.map (fun x -> String x) i.commands)])

let convert_prover_answer (pa: prover_answer) =
  match pa with
  | Valid             -> String "Valid"
  | Invalid           -> String "Invalid"
  | Timeout           -> String "Timeout"
  | OutOfMemory       -> String "OutOfMemory"
  | StepLimitExceeded -> String "StepLimitExceeded"
  | Unknown _         -> String "Unknown"
  | Failure _         -> String "Failure"
  | HighFailure       -> String "HighFailure"

let convert_limit (l: Call_provers.resource_limit) =
  Record (convert_record
    ["limit_time", Int l.Call_provers.limit_time;
     "limit_mem", Int l.Call_provers.limit_mem;
     "limit_steps", Int l.Call_provers.limit_steps])

let convert_unix_process (ps: Unix.process_status) =
  match ps with
  | Unix.WEXITED _   -> String "WEXITED"
  | Unix.WSIGNALED _ -> String "WSIGNALED"
  | Unix.WSTOPPED _  -> String "WSTOPPED"

let convert_model (m: Model_parser.model) =
  String (Pp.string_of (fun fmt m -> Model_parser.print_model fmt m) m)

(* TODO pr_model should have a different format *)
let convert_proof_result (pr: prover_result) =
  Record (convert_record
    ["pr_answer", convert_prover_answer pr.pr_answer;
     "pr_status", convert_unix_process pr.pr_status;
     "pr_output", String pr.pr_output;
     "pr_time", Float pr.pr_time;
     "pr_steps", Int pr.pr_steps;
     "pr_model", convert_model pr.pr_model])

let convert_proof_attempt (pas: proof_attempt_status) =
  Record (match pas with
  | Unedited ->
      convert_record ["proof_attempt", String "Unedited"]
  | JustEdited ->
      convert_record ["proof_attempt", String "JustEdited"]
  | Interrupted ->
      convert_record ["proof_attempt", String "Interrupted"]
  | Scheduled ->
      convert_record ["proof_attempt", String "Scheduled"]
  | Detached ->
      convert_record ["proof_attempt", String "Detached"]
  | Running ->
      convert_record ["proof_attempt", String "Running"]
  | Done pr ->
      convert_record ["proof_attempt", String "Done";
                      "prover_result", convert_proof_result pr]
  | Controller_itp.InternalFailure e ->
      convert_record ["proof_attempt", String "InternalFailure";
                      "exception", String (Pp.string_of Exn_printer.exn_printer e)]
  | Uninstalled p ->
      convert_record ["proof_attempt", String "Uninstalled";
                      "prover", convert_prover_to_json p])

let convert_update u =
  Record (match u with
  | Proved b ->
      convert_record ["update_info", String "Proved";
             "proved", Bool b]
  | Proof_status_change (pas, b, l) ->
      convert_record ["update_info", String "Proof_status_change";
             "proof_attempt", convert_proof_attempt pas;
             "obsolete", Bool b;
             "limit", convert_limit l]
(*
  | Obsolete b ->
      convert_record ["update_info", String "Obsolete";
           "obsolete", Bool b]
*)
         )

let convert_notification_constructor n =
  match n with
  | New_node _                   -> String "New_node"
  | Node_change _                -> String "Node_change"
  | Remove _                     -> String "Remove"
  | Next_Unproven_Node_Id (_, _) -> String "Next_Unproven_Node_Id"
  | Initialized _                -> String "Initialized"
  | Saved                        -> String "Saved"
  | Message _                    -> String "Message"
  | Dead _                       -> String "Dead"
  | Task _                       -> String "Task"
  | File_contents _              -> String "File_contents"

let convert_node_type_string nt =
  match nt with
  | NRoot           -> "NRoot"
  | NFile           -> "NFile"
  | NTheory         -> "NTheory"
  | NTransformation -> "NTransformation"
  | NGoal           -> "NGoal"
  | NProofAttempt   -> "NProofAttempt"

let convert_node_type nt =
  String (convert_node_type_string nt)

let convert_request_constructor (r: ide_request) =
  match r with
  | Command_req _             -> String "Command_req"
(*
  | Prove_req _               -> String "Prove_req"
*)
  | Transform_req _           -> String "Transform_req"
  | Strategy_req _            -> String "Strategy_req"
  | Edit_req _                -> String "Edit_req"
(*
  | Open_session_req _        -> String "Open_session_req"
*)
  | Add_file_req _            -> String "Add_file_req"
  | Save_file_req _           -> String "Save_file_req"
  | Set_max_tasks_req _       -> String "Set_max_tasks_req"
  | Get_file_contents _       -> String "Get_file_contents"
  | Focus_req _               -> String "Focus_req"
  | Unfocus_req               -> String "Unfocus_req"
  | Get_task _                -> String "Get_task"
  | Remove_subtree _          -> String "Remove_subtree"
  | Copy_paste _              -> String "Copy_paste"
  | Copy_detached _           -> String "Copy_detached"
  | Get_first_unproven_node _ -> String "Get_first_unproven_node"
  | Get_Session_Tree_req      -> String "Get_Session_Tree_req"
  | Mark_obsolete_req _       -> String "Mark_obsolete_req"
  | Clean_req                 -> String "Clean_req"
  | Save_req                  -> String "Save_req"
  | Reload_req                -> String "Reload_req"
  | Replay_req                -> String "Replay_req"
  | Exit_req                  -> String "Exit_req"
  | Interrupt_req             -> String "Interrupt_req"

let print_request_to_json (r: ide_request): Json_base.json =
  let cc = convert_request_constructor in
  Record (
  match r with
  | Command_req (nid, s) ->
      convert_record ["ide_request", cc r;
           "node_ID", Int nid;
           "command", String s]
(*
  | Prove_req (nid, p, l) ->
      convert_record ["ide_request", cc r;
           "node_ID", Int nid;
           "prover", String p;
           "limit", convert_limit l]
*)
  | Transform_req (nid, tr, args) ->
      convert_record ["ide_request", cc r;
           "node_ID", Int nid;
           "transformation", String tr;
           "arguments", List (List.map (fun x -> String x) args)]
  | Strategy_req (nid, str) ->
      convert_record ["ide_request", cc r;
           "node_ID", Int nid;
           "strategy", String str]
  | Edit_req (nid, prover) ->
      convert_record ["ide_request", cc r;
                      "node_ID", Int nid;
                      "prover", String prover]
(*
  | Open_session_req f ->
      convert_record ["ide_request", cc r;
           "file", String f]
*)
  | Add_file_req f ->
      convert_record ["ide_request", cc r;
           "file", String f]
  | Save_file_req (f,_) ->
      convert_record ["ide_request", cc r;
           "file", String f]
  | Set_max_tasks_req n ->
      convert_record ["ide_request", cc r;
           "tasks", Int n]
  | Get_task(n,b,loc) ->
      convert_record ["ide_request", cc r;
           "node_ID", Int n; "do_intros", Bool b; "loc", Bool loc]
  | Get_file_contents s ->
      convert_record ["ide_request", cc r;
           "file", String s]
  | Remove_subtree n ->
      convert_record ["ide_request", cc r;
           "node_ID", Int n]
  | Copy_paste (from_id, to_id) ->
      convert_record ["ide_request", cc r;
           "node_ID1", Int from_id;
           "node_ID2", Int to_id]
  | Copy_detached from_id ->
      convert_record ["ide_request", cc r;
           "node_ID", Int from_id]
  | Get_first_unproven_node id ->
      convert_record ["ide_request", cc r;
           "node_ID", Int id]
  | Focus_req id ->
      convert_record ["ide_request", cc r;
                      "node_ID", Int id]
  | Unfocus_req ->
      convert_record ["ide_request", cc r]
  | Get_Session_Tree_req ->
      convert_record ["ide_request", cc r]
  | Mark_obsolete_req n ->
      convert_record ["ide_request", cc r;
           "node_ID", Int n]
  | Clean_req ->
      convert_record ["ide_request", cc r]
  | Save_req ->
      convert_record ["ide_request", cc r]
  | Reload_req ->
      convert_record ["ide_request", cc r]
  | Replay_req ->
      convert_record ["ide_request", cc r]
  | Exit_req ->
      convert_record ["ide_request", cc r]
  | Interrupt_req ->
      convert_record ["ide_request", cc r])

let convert_constructor_message (m: message_notification) =
  match m with
  | Proof_error _         -> String "Proof_error"
  | Transf_error _        -> String "Transf_error"
  | Strat_error _         -> String "Strat_error"
  | Replay_Info _         -> String "Replay_Info"
  | Query_Info _          -> String "Query_Info"
  | Query_Error _         -> String "Query_Error"
  | Help _                -> String "Help"
  | Information _         -> String "Information"
  | Task_Monitor _        -> String "Task_Monitor"
  | Parse_Or_Type_Error _ -> String "Parse_Or_Type_Error"
  | Error _               -> String "Error"
  | Open_File_Error _     -> String "Open_File_Error"
  | File_Saved _          -> String "File_Saved"

let convert_loc (loc: Loc.position) : Json_base.json =
  let (file, line, col1, col2) = Loc.get loc in
  Record (convert_record ["file", Json_base.String file;
                          "line", Json_base.Int line;
                          "col1", Json_base.Int col1;
                          "col2", Json_base.Int col2])

let convert_message (m: message_notification) =
  let cc = convert_constructor_message in
  Record (match m with
  | Proof_error (nid, s) ->
      convert_record ["mess_notif", cc m;
           "node_ID", Int nid;
           "error", String s]
  | Transf_error (nid, tr, arg, loc, s, doc) ->
      convert_record ["mess_notif", cc m;
           "node_ID", Int nid;
           "tr_name", String tr;
           "failing_arg", String arg;
           "loc", convert_loc loc;
           "error", String s;
           "doc", String doc]
  | Strat_error (nid, s) ->
      convert_record ["mess_notif", cc m;
           "node_ID", Int nid;
           "error", String s]
  | Replay_Info s ->
      convert_record ["mess_notif", cc m;
           "replay_info", String s]
  | Query_Info (nid, s) ->
      convert_record ["mess_notif", cc m;
           "node_ID", Int nid;
           "qinfo", String s]
  | Query_Error (nid, s) ->
      convert_record ["mess_notif", cc m;
           "node_ID", Int nid;
           "qerror", String s]
  | Help s ->
      convert_record ["mess_notif", cc m;
           "qhelp", String s]
  | Information s ->
      convert_record ["mess_notif", cc m;
           "information", String s]
  | Task_Monitor (n, k, p) ->
      convert_record ["mess_notif", cc m;
           "monitor", List [Int n; Int k; Int p]]
  | Parse_Or_Type_Error (loc, s) ->
      convert_record ["mess_notif", cc m;
                      "loc", convert_loc loc;
                      "error", String s]
  | Error s ->
      convert_record ["mess_notif", cc m;
           "error", String s]
  | Open_File_Error s ->
      convert_record ["mess_notif", cc m;
           "open_error", String s]
  | File_Saved s ->
      convert_record ["mess_notif", cc m;
           "information", String s])

let convert_color (color: color) : Json_base.json =
  Json_base.String (
    match color with
    | Neg_premise_color -> "Neg_premise_color"
    | Premise_color -> "Premise_color"
    | Goal_color -> "Goal_color")

let convert_loc_color (loc,color: Loc.position * color) : Json_base.json =
  let loc = convert_loc loc in
  let color = convert_color color in
  Record (convert_record ["loc", loc; "color", color])

let convert_list_loc (l: (Loc.position * color) list) : json =
  let list_of_loc = List.map convert_loc_color l in
  List list_of_loc

exception Notcolor

let parse_color (j: json) : color =
  match j with
  | String "Neg_premise_color" -> Neg_premise_color
  | String "Premise_color"     -> Premise_color
  | String "Goal_color"        -> Goal_color
  | _ -> raise Notcolor

exception Notposition

let parse_loc (j: json) : Loc.position =
  try
    let file = get_string (get_field j "file") in
    let line = get_int (get_field j "line") in
    let col1 = get_int (get_field j "col1") in
    let col2 = get_int (get_field j "col2") in
    Loc.user_position file line col1 col2
  with
    Not_found -> raise Notposition

let parse_loc_color (j: json): Loc.position * color =
  let loc = parse_loc j in
  let color = parse_color j in
  (loc, color)

let parse_list_loc (j: json): (Loc.position * color) list =
  match j with
  | List l -> List.map parse_loc_color l
  | _ -> raise Notposition

let print_notification_to_json (n: notification): json =
  let cc = convert_notification_constructor in
  Record (
  match n with
  | New_node (nid, parent, node_type, name, detached) ->
      convert_record ["notification", cc n;
           "node_ID", Int nid;
           "parent_ID", Int parent;
           "node_type", convert_node_type node_type;
           "name", String name;
           "detached", Bool detached]
  | Node_change (nid, update) ->
      convert_record ["notification", cc n;
           "node_ID", Int nid;
           "update", convert_update update]
  | Remove nid ->
      convert_record ["notification", cc n;
           "node_ID", Int nid]
  | Next_Unproven_Node_Id (from_id, unproved_id) ->
      convert_record ["notification", cc n;
           "node_ID1", Int from_id;
           "node_ID2", Int unproved_id]
  | Initialized infos ->
      convert_record ["notification", cc n;
           "infos", convert_infos infos]
  | Saved ->
      convert_record ["notification", cc n]
  | Message m ->
      convert_record ["notification", cc n;
           "message", convert_message m]
  | Dead s ->
      convert_record ["notification", cc n;
           "message", String s]
  | Task (nid, s, list_loc) ->
      convert_record ["notification", cc n;
           "node_ID", Int nid;
           "task", String s;
           "list_loc", convert_list_loc list_loc]
  | File_contents (f, s) ->
      convert_record ["notification", cc n;
           "file", String f;
           "content", String s])

let print_notification fmt (n: notification) =
  Format.fprintf fmt "%a" print_json (print_notification_to_json n)

let print_request fmt (r: ide_request) =
  Format.fprintf fmt "%a" print_json (print_request_to_json r)

let print_list_notification fmt (nl: notification list) =
  Format.fprintf fmt "%a" (Json_base.list print_notification) nl

let print_list_request fmt (rl: ide_request list) =
  Format.fprintf fmt "%a" (Json_base.list print_request) rl

exception NotProver

let parse_prover_from_json (j: json) =
  try
    let pn = get_string (get_field j "prover_name") in
    let pv = get_string (get_field j "prover_version") in
    let pa = get_string (get_field j "prover_altern") in
    {Whyconf.prover_name = pn; prover_version = pv; prover_altern = pa}
  with Not_found -> raise NotProver

exception NotLimit

let parse_limit_from_json (j: json) =
  try
    let t = get_int (get_field j "limit_time") in
    let m = get_int (get_field j "limit_mem") in
    let s = get_int (get_field j "limit_steps") in
    {limit_time = t; limit_mem = m; limit_steps = s}
  with Not_found -> raise NotLimit

exception NotRequest of string

let parse_request (constr: string) j =
  match constr with
  | "Command_req" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "command") in
    Command_req (nid, s)
(*
  | "Prove_req" ->
    let nid = get_int (get_field j "node_ID") in
    let p = get_string (get_field j "prover") in
    let l = get_field j "limit" in
    Prove_req (nid, p, parse_limit_from_json l)
 *)
  | "Transform_req" ->
    let nid = get_int (get_field j "node_ID") in
    let tr = get_string (get_field j "transformation") in
    let args = get_list (get_field j "arguments") in
    Transform_req (nid, tr,
                   List.map (fun x ->
                     match x with
                     | String t -> t
                     | _ -> raise (NotRequest "")) args)

  | "Strategy_req" ->
    let nid = get_int (get_field j "node_ID") in
    let str = get_string (get_field j "strategy") in
    Strategy_req (nid, str)

  | "Edit_req" ->
    let nid = get_int (get_field j "node_ID") in
    let p = get_string (get_field j "prover") in
    Edit_req (nid, p)
(*
  | "Open_session_req" ->
    let f = get_string (get_field j "file") in
    Open_session_req f
*)
  | "Focus_req" ->
    let nid = get_int (get_field j "node_ID") in
    Focus_req nid

  | "Unfocus_req" ->
    Unfocus_req

  | "Get_first_unproven_node" ->
    let nid = get_int (get_field j "node_ID") in
    Get_first_unproven_node nid

  | "Add_file_req" ->
    let f = get_string (get_field j "file") in
    Add_file_req f

  | "Set_max_tasks_req" ->
    let n = get_int (get_field j "tasks") in
    Set_max_tasks_req n

  | "Get_task" ->
    let n = get_int (get_field j "node_ID") in
    let b = get_bool_opt (get_field j "do_intros") false in
    let loc = get_bool_opt (get_field j "loc") false in
    Get_task(n,b,loc)

  | "Remove_subtree" ->
    let n = get_int (get_field j "node_ID") in
    Remove_subtree n

  | "Copy_paste" ->
    let from_id = get_int (get_field j "node_ID1") in
    let to_id = get_int (get_field j "node_ID2") in
    Copy_paste (from_id, to_id)

  | "Copy_detached" ->
    let n = get_int (get_field j "node_ID") in
    Copy_detached n

  | "Get_Session_Tree_req" ->
    Get_Session_Tree_req

  | "Mark_obsolete_req" ->
    let n = get_int (get_field j "node_ID") in
    Mark_obsolete_req n
  | "Clean_req" ->
    Clean_req
  | "Save_req" ->
    Save_req
  | "Reload_req" ->
    Reload_req
  | "Replay_req" ->
    Replay_req
  | "Exit_req" ->
    Exit_req
  | _ -> raise (NotRequest "")

let parse_request_json (j: json): ide_request =
  try
    let constr = get_string (get_field j "ide_request") in
    parse_request constr j
  with
  | _ -> let s =Pp.string_of print_json j in
    begin Format.eprintf "BEGIN \n %s \nEND\n@." s; raise (NotRequest s); end

exception NotNodeType

let parse_node_type_from_json j =
  match j with
  | String "NRoot"           -> NRoot
  | String "NFile"           -> NFile
  | String "NTheory"         -> NTheory
  | String "NTransformation" -> NTransformation
  | String "NGoal"           -> NGoal
  | String "NProofAttempt"   -> NProofAttempt
  | _                        -> raise NotNodeType

exception NotProverAnswer

let parse_prover_answer j =
  match j with
  | String "Valid"             -> Valid
  | String "Invalid"           -> Invalid
  | String "Timeout"           -> Timeout
  | String "OutOfMemory"       -> OutOfMemory
  | String "StepLimitExceeded" -> StepLimitExceeded
  | String "Unknown"           -> raise NotProverAnswer (* TODO *)
  | String "Failure"           -> raise NotProverAnswer (* TODO *)
  | String "HighFailure"       -> HighFailure
  | _                          -> raise NotProverAnswer

exception NotUnixProcess

let parse_unix_process j =
  match j with
  | String "WEXITED" -> Unix.WEXITED 0 (* TODO dummy value *)
  | String "WSIGNALED" -> Unix.WSIGNALED 0 (* TODO dummy value *)
  | String "WSTOPPED" -> Unix.WSTOPPED 0 (* TODO dummy value *)
  | _ -> raise NotUnixProcess

exception NotProverResult

let parse_prover_result j =
  try
    let pr_answer = get_field j "pr_answer" in
    let pr_status_unix = get_field j "pr_status" in
    let pr_output = get_string (get_field j "pr_output") in
    let pr_time = get_float (get_field j "pr_time") in
    let pr_steps = get_int (get_field j "pr_steps") in
    let pr_model = get_string (get_field j "pr_model") in
    {pr_answer = parse_prover_answer pr_answer;
     pr_status = parse_unix_process pr_status_unix;
     pr_output = pr_output;
     pr_time = pr_time;
     pr_steps = pr_steps;
     pr_model = Obj.magic pr_model} (* TODO pr_model is a string, should be model *)
  with
  | _ -> raise NotProverResult

exception NotProofAttempt

let parse_proof_attempt j =
  let s = get_string (get_field j "proof_attempt") in
  match s with
  | "Unedited" -> Unedited
  | "JustEdited" -> JustEdited
  | "Interrupted" -> Interrupted
  | "Scheduled" -> Scheduled
  | "Running" -> Running
  | "Done" ->
    let pr = get_field j "prover_result" in
    Done (parse_prover_result pr)
  | "InternalFailure" ->
    raise NotProofAttempt (* TODO *)
  | "Uninstalled" ->
    let p = get_field j "prover" in
    Uninstalled (parse_prover_from_json p)
  | _ -> raise NotProofAttempt

exception NotUpdate

let parse_update j =
  let update = get_string (get_field j "update_info") in
  match update with
  | "Proved" ->
    let b = get_bool (get_field j "proved") in
    Proved b
  | "Proof_status_change" ->
    let pas = get_field j "proof_attempt" in
    let b = get_bool (get_field j "obsolete") in
    let l = get_field j "limit" in
    Proof_status_change (parse_proof_attempt pas, b, parse_limit_from_json l)
(*
  | "Obsolete" ->
    let b = get_bool (get_field j "obsolete") in
    Obsolete b
*)
  | _ -> raise NotUpdate

exception NotInfos

let parse_infos j =
  try
    let pr = get_list (get_field j "provers") in
    let tr = get_list (get_field j "transformations") in
    let str = get_list (get_field j "strategies") in
    let com = get_list (get_field j "commands") in
    {provers = List.map (fun j -> try
                                 (get_string (get_field j "prover_shortcut"),
                                  get_string (get_field j "prover_name"))
                               with Not_found -> raise NotInfos) pr;
     transformations = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) tr;
     strategies = List.map (fun j -> try
                                 (get_string (get_field j "strategy_shortcut"),
                                  get_string (get_field j "strategy_name"))
                               with Not_found -> raise NotInfos) str;
     commands = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) com}
  with _ -> raise NotInfos

exception NotMessage

let parse_message constr j =
  match constr with
  | "Proof_error" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "error") in
    Proof_error (nid, s)

  | "Transf_error" ->
    let nid = get_int (get_field j "node_ID") in
    let tr_name = get_string (get_field j "tr_name") in
    let arg = get_string (get_field j "failing_arg") in
    let loc = parse_loc (get_field j "loc") in
    let error = get_string (get_field j "error") in
    let doc = get_string (get_field j "doc") in
    Transf_error (nid, tr_name, arg, loc, error, doc)

  | "Strat_error" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "error") in
    Strat_error (nid, s)

  | "Replay_Info" ->
    let s = get_string (get_field j "replay_info") in
    Replay_Info s
  | "Query_Info" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "qinfo") in
    Query_Info (nid, s)

  | "Query_Error" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "qerror") in
    Query_Error (nid, s)

  | "Help" ->
    let s = get_string (get_field j "qhelp") in
    Help s

  | "Information" ->
    let s = get_string (get_field j "information") in
    Information s

  | "Task_Monitor" ->
    let m = get_list (get_field j "monitor") in
    begin
      match m with
      | Int n :: Int k :: Int p :: [] -> Task_Monitor (n, k, p)
      | _ -> raise NotMessage
    end

  | "Error" ->
    let s = get_string (get_field j "error") in
    Error s

  | "Open_File_Error" ->
    let s = get_string (get_field j "open_error") in
    Open_File_Error s

  | "Parse_Or_Type_Error" ->
    let loc = parse_loc (get_field j "loc") in
    let error = get_string (get_field j "error") in
    Parse_Or_Type_Error (loc, error)

  | _ -> raise NotMessage


let parse_message j =
  let constr = get_string (get_field j "mess_notif") in
  parse_message constr j

exception NotNotification of string

let parse_notification constr j =
  match constr with
  | "New_node" ->
    let nid = get_int (get_field j "node_ID") in
    let parent = get_int (get_field j "parent_ID") in
    let node_type = get_field j "node_type" in
    let name = get_string (get_field j "name") in
    let detached = get_bool (get_field j "detached") in
    New_node (nid, parent, parse_node_type_from_json node_type, name, detached)

  | "Node_change" ->
    let nid = get_int (get_field j "node_ID") in
    let update = get_field j "update" in
    Node_change (nid, parse_update update)

  | "Remove" ->
    let nid = get_int (get_field j "node_ID") in
    Remove nid

  | "Initialized" ->
    let infos = get_field j "infos" in
    Initialized (parse_infos infos)

  | "Saved" -> Saved

  | "Message" ->
    let m = get_field j "message" in
    Message (parse_message m)

  | "Dead" ->
    let s = get_string (get_field j "message") in
    Dead s

  | "Task" ->
    let nid = get_int (get_field j "node_ID") in
    let s = get_string (get_field j "task") in
    let l = get_field j "loc_list" in
    Task (nid, s, parse_list_loc l)

  | "Next_Unproven_Node_Id" ->
    let nid1 = get_int (get_field j "node_ID1") in
    let nid2 = get_int (get_field j "node_ID2") in
    Next_Unproven_Node_Id (nid1, nid2)

  | "File_contents" ->
    let f = get_string (get_field j "file") in
    let s = get_string (get_field j "content") in
    File_contents(f,s)

  | s -> raise (NotNotification ("<from parse_notification> " ^ s))

let parse_notification_json j =
  try
    let constr = get_string (get_field j "notification") in
    parse_notification constr j
  with
  | _ -> raise (NotNotification "<from parse_notification_json>")

let parse_json_object (s: string) =
  let lb = Lexing.from_string s in
  let x = Json_parser.value (fun x -> Json_lexer.read x) lb in
  x

let parse_notification (s: string) : notification =
  let json = parse_json_object s in
  parse_notification_json json

let parse_request (s: string) : ide_request =
  let json = parse_json_object s in
  parse_request_json json


let parse_list_notification (s: string): notification list =
  let json = parse_json_object s in
  match json with
  | List [Null] -> []
  | List l -> List.map parse_notification_json l
  | _ -> []

let parse_list_request (s: string): ide_request list =
  let json = parse_json_object s in
  match json with
  | List l -> List.map parse_request_json l
  | _ -> raise (NotRequest "Not list")
