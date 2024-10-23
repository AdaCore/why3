(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
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

let convert_prover_aux (prefix:string) (p: Whyconf.prover) =
  [prefix ^ "name", String p.Whyconf.prover_name;
   prefix ^ "version", String p.Whyconf.prover_version;
   prefix ^ "altern", String p.Whyconf.prover_altern]

let convert_prover (prefix:string) (p: Whyconf.prover) =
  Record (convert_prover_aux prefix p)

let convert_infos (i: global_information) =
  let convert_prover (s,h,p) =
    Record
      ["prover_shortcut", String s;
       "prover_name", String h;
       "prover_parseable_name", String p]
  in
  let convert_strategy (s,p) =
    Record
      ["strategy_shortcut", String s;
       "strategy_name", String p]
  in
  Record
    ["provers", List (List.map convert_prover i.provers);
     "transformations",
     List (List.map
             (fun (a, b) ->
               Record ["name_t", String a; "desc_t", String b])
             i.transformations);
     "strategies", List (List.map convert_strategy i.strategies);
     "commands", List (List.map (fun x -> String x) i.commands)]

let convert_prover_answer (pa: prover_answer) =
  match pa with
  | Valid             -> "Valid",""
  | Invalid           -> "Invalid",""
  | Timeout           -> "Timeout",""
  | OutOfMemory       -> "OutOfMemory",""
  | StepLimitExceeded -> "StepLimitExceeded",""
  | Unknown s         -> "Unknown",s
  | Failure s         -> "Failure",s
  | HighFailure s     -> "HighFailure",s

let convert_limit (l: Call_provers.resource_limits) =
  Record
    ["limit_time", Float l.Call_provers.limit_time;
     "limit_mem", Int l.Call_provers.limit_mem;
     "limit_steps", Int l.Call_provers.limit_steps]

let convert_unix_process (ps: Unix.process_status) =
  match ps with
  | Unix.WEXITED n   -> "WEXITED", n
  | Unix.WSIGNALED n -> "WSIGNALED", n
  | Unix.WSTOPPED n  -> "WSTOPPED", n

let convert_model (m: Model_parser.model) =
  String (Pp.string_of
            (fun fmt m -> Model_parser.print_model ~print_attrs:true fmt m) m)

let convert_models (ml: Model_parser.model list) =
  List (List.map convert_model ml)

(* TODO pr_model should have a different format *)
let convert_proof_result (pr: prover_result) =
  let (a,s) = convert_prover_answer pr.pr_answer in
  let (us,ua) = convert_unix_process pr.pr_status in
  Record
    ["pr_answer", String a;
     "pr_answer_arg", String s;
     "pr_status", String us;
     "pr_status_arg", Int ua;
     "pr_output", String pr.pr_output;
     "pr_time", Float pr.pr_time;
     "pr_steps", Int pr.pr_steps;
     "pr_models", convert_models (List.map snd pr.pr_models)] (* TODO print also prover_answer? *)

let convert_proof_attempt (pas: proof_attempt_status) =
  Record (match pas with
  | Undone -> ["proof_attempt", String "Undone"]
  | Interrupted -> ["proof_attempt", String "Interrupted"]
  | Scheduled -> ["proof_attempt", String "Scheduled"]
  | Detached -> ["proof_attempt", String "Detached"]
  | Running -> ["proof_attempt", String "Running"]
  | Done pr ->
      ["proof_attempt", String "Done";
       "prover_result", convert_proof_result pr]
  | Controller_itp.InternalFailure e ->
      ["proof_attempt", String "InternalFailure";
       "exception", String (Pp.string_of Exn_printer.exn_printer e)]
  | Uninstalled p ->
      ["proof_attempt", String "Uninstalled";
       "prover", convert_prover "prover_" p]
  | Removed p ->
      ["proof_attempt", String "Removed";
       "prover", convert_prover "prover_" p]
  | UpgradeProver p ->
      ["proof_attempt", String "UpgradeProver";
       "prover", convert_prover "prover_" p])

let convert_update u =
  Record (match u with
  | Proved b ->
      ["update_info", String "Proved";
       "proved", Bool b]
  | Name_change n ->
      ["update_info", String "Name_change";
       "name", String n]
  | Proof_status_change (pas, b, l) ->
      ["update_info", String "Proof_status_change";
       "proof_attempt", convert_proof_attempt pas;
       "obsolete", Bool b;
       "limit", convert_limit l]
  )

let convert_node_type nt =
  String (match nt with
  | NRoot           -> "NRoot"
  | NFile           -> "NFile"
  | NTheory         -> "NTheory"
  | NTransformation -> "NTransformation"
  | NGoal           -> "NGoal"
  | NProofAttempt   -> "NProofAttempt"
  )

let convert_loc (loc: Loc.position) : Json_base.json =
  let (file, sline, scol, eline, ecol) = Loc.get loc in
  Record
    ["file-name", Json_base.String file;
     "start-line", Json_base.Int sline;
     "start-col", Json_base.Int scol;
     "end-line", Json_base.Int eline;
     "end-col", Json_base.Int ecol]

open Whyconf

let convert_policy u =
  match u with
  | CPU_remove -> ["policy", String "remove"]
  | CPU_keep -> ["policy", String "keep"]
  | CPU_upgrade p ->
     ["policy", String "upgrade"] @ convert_prover_aux "target_" p
  | CPU_duplicate p ->
     ["policy", String "duplicate"] @ convert_prover_aux "target_" p

let convert_strat str =
  String (match str with
      | Next -> "Next"
      | Prev -> "Prev"
      | Clever -> "Clever")

let parse_strat j =
  match j with
  | String "Next" -> Next
  | String "Prev" -> Prev
  | String "Clever" -> Clever
  | _ -> assert false

let convert_config_param (p : config_param)  =
  match p with
  | Max_tasks m -> ["param", String "max_tasks"; "value", Int m]
  | Timelimit f -> ["param", String "timelimit"; "value", Float f]
  | Memlimit m ->  ["param", String "memlimit"; "value", Int m]

let convert_request (r: ide_request): Json_base.json =
  Record (
  match r with
  | Command_req (nid, s) ->
      ["ide_request", String "Command_req";
       "node_ID", Int nid;
       "command", String s]
  | Add_file_req f ->
      ["ide_request", String "Add_file_req";
       "file", String f]
  | Save_file_req (f,_) ->
      ["ide_request", String "Save_file_req";
       "file", String f]
  | Set_config_param p ->
      ["ide_request", String "Set_config_param"] @ convert_config_param p
  | Set_prover_policy(p,u) ->
      ["ide_request", String "Set_prover_policy"] @
        convert_prover_aux "" p @ convert_policy u
  | Get_task(n,b,show_uses_clones_metas,loc) ->
      ["ide_request", String "Get_task";
       "node_ID", Int n;
       "full_context", Bool b;
       "show_uses_clones_metas", Bool show_uses_clones_metas;
       "loc", Bool loc]
  | Get_file_contents s ->
      ["ide_request", String "Get_file_contents";
       "file", String s]
  | Find_ident_req loc ->
      ["ide_request", String "Find_ident_req";
       "loc", convert_loc loc]
  | Remove_subtree n ->
      ["ide_request", String "Remove_subtree";
       "node_ID", Int n]
  | Copy_paste (from_id, to_id) ->
      ["ide_request", String "Copy_paste";
       "node_ID1", Int from_id;
       "node_ID2", Int to_id]
  | Get_first_unproven_node (str, id) ->
      ["ide_request", String "Get_first_unproven_node";
       "node_ID", Int id;
       "strat", convert_strat str]
  | Check_need_saving_req ->
      ["ide_request", String "Check_need_saving_req"]
  | Unfocus_req ->
      ["ide_request", String "Unfocus_req"]
  | Save_req ->
      ["ide_request", String "Save_req"]
  | Export_as_zip ->
      ["ide_request", String "Export_as_zip"]
  | Reload_req ->
      ["ide_request", String "Reload_req"]
  | Exit_req ->
      ["ide_request", String "Exit_req"]
  | Interrupt_req ->
      ["ide_request", String "Interrupt_req"]
  | Reset_proofs_req ->
      ["ide_request", String "Reset_proofs_req"]
  | Get_global_infos ->
      ["ide_request", String "Get_global_infos"])

(* Converted to a Json list for simplicity *)
let convert_option_loc (loc: Loc.position option) : Json_base.json =
  let l =
    match loc with
    | None -> []
    | Some loc -> [convert_loc loc]
  in
  List l

let convert_message (m: message_notification) =
  Record (match m with
  | Proof_error (nid, s) ->
      ["mess_notif", String "Proof_error";
       "node_ID", Int nid;
       "error", String s]
  | Transf_error (is_fatal, nid, tr, arg, loc, s, doc) ->
      ["mess_notif", String "Transf_error";
       "is_fatal", Bool is_fatal;
       "node_ID", Int nid;
       "tr_name", String tr;
       "failing_arg", String arg;
       "loc", convert_loc loc;
       "error", String s;
       "doc", String doc]
  | Strat_error (nid, s) ->
      ["mess_notif", String "Strat_error";
       "node_ID", Int nid;
       "error", String s]
  | Replay_Info s ->
      ["mess_notif", String "Replay_Info";
       "replay_info", String s]
  | Query_Info (nid, s) ->
      ["mess_notif", String "Query_Info";
       "node_ID", Int nid;
       "qinfo", String s]
  | Query_Error (nid, s) ->
      ["mess_notif", String "Query_Error";
       "node_ID", Int nid;
       "qerror", String s]
  | Information s ->
      ["mess_notif", String "Information";
       "information", String s]
  | Task_Monitor (n, k, p) ->
      ["mess_notif", String "Task_Monitor";
       "monitor", List [Int n; Int k; Int p]]
  | Parse_Or_Type_Error (loc, rel_loc,s) ->
      ["mess_notif", String "Parse_Or_Type_Error";
       "loc", convert_loc loc;
       "rel_loc", convert_loc rel_loc;
       "error", String s]
  | Error s ->
      ["mess_notif", String "Error";
       "error", String s]
  | Open_File_Error s ->
      ["mess_notif", String "Open_File_Error";
       "open_error", String s]
  | File_Saved s ->
      ["mess_notif", String "File_Saved";
       "information", String s])

let convert_color (color: color) : Json_base.json =
  Json_base.String (
    match color with
    | Neg_premise_color -> "Neg_premise_color"
    | Premise_color     -> "Premise_color"
    | Goal_color        -> "Goal_color"
    | Error_color       -> "Error_color"
    | Error_line_color  -> "Error_line_color"
    | Error_font_color  -> "Error_font_color"
    | Search_color      -> "Search_color"
  )

let convert_loc_color (loc,color: Loc.position * color) : Json_base.json =
  let loc = convert_loc loc in
  let color = convert_color color in
  Record ["loc", loc; "color", color]

let convert_list_loc (l: (Loc.position * color) list) : json =
  let list_of_loc = List.map convert_loc_color l in
  List list_of_loc

exception Notcolor

let parse_color (j: json) : color =
  match j with
  | String "Neg_premise_color" -> Neg_premise_color
  | String "Premise_color"     -> Premise_color
  | String "Goal_color"        -> Goal_color
  | String "Error_color"       -> Error_color
  | String "Error_line_color"  -> Error_line_color
  | String "Error_font_color"  -> Error_font_color
  | String "Search_color"      -> Search_color
  | _ -> raise Notcolor

exception Notposition

let parse_loc (j: json) : Loc.position =
  try
    let file = get_string_field j "file-name" in
    let sline = get_int_field j "start-line" in
    let scol = get_int_field j "start-col" in
    let eline = get_int_field j "end-line" in
    let ecol = get_int_field j "end-col" in
    Loc.user_position file sline scol eline ecol
  with
    Not_found -> raise Notposition

let parse_loc_color (j: json): Loc.position * color =
  try
    let loc = parse_loc (get_field j "loc") in
    let color = parse_color (get_field j "color") in
    (loc, color)
  with
    Not_found -> raise Notposition

let parse_list_loc (j: json): (Loc.position * color) list =
  match j with
  | List l -> List.map parse_loc_color l
  | _ -> raise Notposition

(* Option is represented by a list *)
let parse_opt_loc (j: json): Loc.position option =
  match j with
  | List [] -> None
  | List [loc] -> Some (parse_loc loc)
  | _ -> None (* Ignore this case that should not happen *)

let convert_notification (n: notification): json =
  Record (
  match n with
  | Reset_whole_tree ->
      ["notification", String "Reset_whole_tree"]
  | New_node (nid, parent, node_type, name, detached) ->
      ["notification", String "New_node";
       "node_ID", Int nid;
       "parent_ID", Int parent;
       "node_type", convert_node_type node_type;
       "name", String name;
       "detached", Bool detached]
  | Node_change (nid, update) ->
      ["notification", String "Node_change";
       "node_ID", Int nid;
       "update", convert_update update]
  | Remove nid ->
      ["notification", String "Remove";
       "node_ID", Int nid]
  | Next_Unproven_Node_Id (from_id, unproved_id) ->
      ["notification", String "Next_Unproven_Node_Id";
       "node_ID1", Int from_id;
       "node_ID2", Int unproved_id]
  | Initialized infos ->
      ["notification", String "Initialized";
       "infos", convert_infos infos]
  | Saved ->
      ["notification", String "Saved"]
  | Saving_needed b ->
      ["notification", String "Saving_needed";
       "need_saving", Bool b]
  | Message m ->
      ["notification", String "Message";
       "message", convert_message m]
  | Dead s ->
      ["notification", String "Dead";
       "message", String s]
  | Task (nid, s, list_loc, goal_loc, lang) ->
      ["notification", String "Task";
       "node_ID", Int nid;
       "task", String s;
       "loc_list", convert_list_loc list_loc;
       "goal_loc", convert_option_loc goal_loc;
       "lang", String lang]
  | File_contents (f, s, f_format, read_only) ->
      ["notification", String "File_contents";
       "file", String f;
       "content", String s;
       "file_format", String f_format;
       "read_only", Bool read_only]
  | Source_and_ce (s, list_loc, goal_loc, f_format) ->
      ["notification", String "Source_and_ce";
       "content", String s;
       "loc_list", convert_list_loc list_loc;
       "goal_loc", convert_option_loc goal_loc;
       "file_format", String f_format]
  | Ident_notif_loc loc ->
      ["notification", String "Ident_notif_loc";
       "ident_loc", convert_loc loc]
)

let print_notification fmt (n: notification) =
  print_json fmt (convert_notification n)

let print_request fmt (r: ide_request) =
  print_json fmt (convert_request r)

let print_list_notification fmt (nl: notification list) =
  Json_base.list print_notification fmt nl

let print_list_request fmt (rl: ide_request list) =
  Json_base.list print_request fmt rl

exception NotProver

let parse_prover_from_json (prefix:string) (j: json) =
  try
    let pn = get_string_field j (prefix ^ "name") in
    let pv = get_string_field j (prefix ^ "version") in
    let pa = get_string_field j (prefix ^ "altern") in
    {Whyconf.prover_name = pn; prover_version = pv; prover_altern = pa}
  with Not_found -> raise NotProver

exception NotLimit

let parse_limit_from_json (j: json) =
  try
    let t = get_float_field j "limit_time" in
    let m = get_int_field j "limit_mem" in
    let s = get_int_field j "limit_steps" in
    {limit_time = t; limit_mem = m; limit_steps = s}
  with Not_found -> raise NotLimit

exception NotRequest of string

let parse_request (constr: string) j =
  match constr with
  | "Command_req" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "command" in
    Command_req (nid, s)

  | "Get_first_unproven_node" ->
    let nid = get_int_field j "node_ID" in
    let str = parse_strat (get_field j "strat") in
    Get_first_unproven_node (str, nid)

  | "Add_file_req" ->
    let f = get_string_field j "file" in
    Add_file_req f

  | "Set_config_param" ->
    let s = get_string_field j "param" in
    let p = begin match s with
      | "max_tasks" -> Max_tasks (get_int_field j "value")
      | "timelimit" -> Timelimit (get_float_field j "value")
      | "memlimit" -> Memlimit (get_int_field j "value")
      | _ -> raise (NotRequest constr)
    end in
    Set_config_param p

  | "Set_prover_policy" ->
    let p = parse_prover_from_json "" j in
    let u = get_string_field j "policy" in
    begin match u with
          | "keep" -> Set_prover_policy(p,CPU_keep)
          | "upgrade" ->
             let p' = parse_prover_from_json "target_" j in
             Set_prover_policy(p,CPU_upgrade p')
          | "duplicate" ->
             let p' = parse_prover_from_json "target_" j in
             Set_prover_policy(p,CPU_duplicate p')
          | _ -> raise (NotRequest "")
    end

  | "Find_ident_req" ->
      let loc = parse_loc (get_field j "loc") in
      Find_ident_req loc

  | "Get_task" ->
    let n = get_int_field j "node_ID" in
    let b = get_bool_opt (get_field j "full_context") false in
    let show_uses_clones_metas = get_bool_opt (get_field j "show_uses_clones_metas") false in
    let loc = get_bool_opt (get_field j "loc") false in
    Get_task(n,b,show_uses_clones_metas,loc)

  | "Remove_subtree" ->
    let n = get_int_field j "node_ID" in
    Remove_subtree n

  | "Copy_paste" ->
    let from_id = get_int_field j "node_ID1" in
    let to_id = get_int_field j "node_ID2" in
    Copy_paste (from_id, to_id)

  | "Unfocus_req" ->
    Unfocus_req
  | "Interrupt_req" ->
    Interrupt_req
  | "Save_req" ->
    Save_req
  | "Export_as_zip" ->
    Export_as_zip
  | "Reload_req" ->
    Reload_req
  | "Reset_proofs_req" ->
    Reset_proofs_req
  | "Exit_req" ->
    Exit_req
  | "Check_need_saving_req" -> Check_need_saving_req
  | "Get_global_infos" -> Get_global_infos
  | _ -> raise (NotRequest constr)

let parse_request_json (j: json): ide_request =
  try
    let constr = get_string_field j "ide_request" in
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

let parse_prover_answer a d =
  match a with
  | "Valid"             -> Valid
  | "Invalid"           -> Invalid
  | "Timeout"           -> Timeout
  | "OutOfMemory"       -> OutOfMemory
  | "StepLimitExceeded" -> StepLimitExceeded
  | "Unknown"           -> Unknown d
  | "Failure"           -> Failure d
  | "HighFailure"       -> HighFailure d
  | _                   -> HighFailure d

let parse_unix_process j arg =
  match j with
  | "WEXITED" -> Unix.WEXITED arg
  | "WSIGNALED" -> Unix.WSIGNALED arg
  | "WSTOPPED" -> Unix.WSTOPPED arg
  | _ -> Unix.WSIGNALED (-1) (* default, should never happen *)

let parse_prover_result j =
  let pr_answer =
    let arg =
      try get_string_field j "pr_answer_arg"
      with Not_found -> ""
    in
    try parse_prover_answer (get_string_field j "pr_answer") arg
    with Not_found -> HighFailure "unparsed prover answer (JSON)"
  in
  let pr_status_unix =
    let arg =
      try get_int_field j "pr_status_arg"
      with Not_found -> (-1)
    in
    try parse_unix_process (get_string_field j "pr_status") arg
    with Not_found -> Unix.WSIGNALED (-1)
  in
  let pr_output =
    try get_string_field j "pr_output"
    with Not_found -> ""
  in
  let pr_time =
    try get_float_field j "pr_time"
    with Not_found -> -1.0
  in
  let pr_steps =
    try get_int_field j "pr_steps"
    with Not_found -> -1
  in
  let _pr_model =
    try get_string_field j "pr_model"
    with Not_found -> ""
  in
  { pr_answer = pr_answer;
    pr_status = pr_status_unix;
    pr_output = pr_output;
    pr_time = pr_time;
    pr_steps = pr_steps;
    pr_models = [] (* pr_model *)}
    (* TODO pr_model is a string, should be model *)

exception NotProofAttempt

let parse_proof_attempt j =
  let s = get_string_field j "proof_attempt" in
  match s with
  | "Undone" -> Undone
  | "Detached" -> Detached
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
    Uninstalled (parse_prover_from_json "prover_" p)
  | "UpgradeProver" ->
    let p = get_field j "prover" in
    UpgradeProver (parse_prover_from_json "prover_" p)
  | _ -> raise NotProofAttempt

exception NotUpdate

let parse_update j =
  let update = get_string_field j "update_info" in
  match update with
  | "Proved" ->
    let b = get_bool_field j "proved" in
    Proved b
  | "Name_change" ->
    let n = get_string_field j "name" in
    Name_change n
  | "Proof_status_change" ->
    let pas = get_field j "proof_attempt" in
    let b = get_bool_field j "obsolete" in
    let l = get_field j "limit" in
    Proof_status_change (parse_proof_attempt pas, b, parse_limit_from_json l)
  | _ -> raise NotUpdate

exception NotInfos of string

let parse_infos j =
  try
    let pr = get_list_field j "provers" in
    let tr = get_list_field j "transformations" in
    let tr =
      List.map (fun j ->
        try
          get_string_field j "name_t",
          get_string_field j "desc_t"
        with | _ -> raise (NotInfos "transformations")) tr in
    let str = get_list_field j "strategies" in
    let com = get_list_field j "commands" in
    {provers = List.map (fun j -> try
                                 (get_string_field j "prover_shortcut",
                                  get_string_field j "prover_name",
                                  get_string_field j "prover_parseable_name")
                               with Not_found -> raise (NotInfos "provers")) pr;
     transformations = tr;
     strategies = List.map (fun j -> try
                                 (get_string_field j "strategy_shortcut",
                                  get_string_field j "strategy_name")
                               with Not_found -> raise (NotInfos "strategies")) str;
     commands = List.map (fun j -> match j with | String x -> x | _ -> raise (NotInfos "commands")) com}
  with Not_found -> raise (NotInfos "infos")

exception NotMessage

let parse_message constr j =
  match constr with
  | "Proof_error" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "error" in
    Proof_error (nid, s)

  | "Transf_error" ->
    let nid = get_int_field j "node_ID" in
    let is_fatal = get_bool_field j "is_fatal" in
    let tr_name = get_string_field j "tr_name" in
    let arg = get_string_field j "failing_arg" in
    let loc = parse_loc (get_field j "loc") in
    let error = get_string_field j "error" in
    let doc = get_string_field j "doc" in
    Transf_error (is_fatal, nid, tr_name, arg, loc, error, doc)

  | "Strat_error" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "error" in
    Strat_error (nid, s)

  | "Replay_Info" ->
    let s = get_string_field j "replay_info" in
    Replay_Info s
  | "Query_Info" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "qinfo" in
    Query_Info (nid, s)

  | "Query_Error" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "qerror" in
    Query_Error (nid, s)

  | "Information" ->
    let s = get_string_field j "information" in
    Information s

  | "Task_Monitor" ->
    let m = get_list_field j "monitor" in
    begin
      match m with
      | Int n :: Int k :: Int p :: [] -> Task_Monitor (n, k, p)
      | _ -> raise NotMessage
    end

  | "Error" ->
    let s = get_string_field j "error" in
    Error s

  | "Open_File_Error" ->
    let s = get_string_field j "open_error" in
    Open_File_Error s

  | "Parse_Or_Type_Error" ->
    let loc = parse_loc (get_field j "loc") in
    let rel_loc = parse_loc (get_field j "rel_loc") in
    let error = get_string_field j "error" in
    Parse_Or_Type_Error (loc, rel_loc, error)

  | _ -> raise NotMessage


let parse_message j =
  let constr = get_string_field j "mess_notif" in
  parse_message constr j

exception NotNotification of string

let parse_notification constr j =
  match constr with
  | "Reset_whole_tree" -> Reset_whole_tree

  | "New_node" ->
    let nid = get_int_field j "node_ID" in
    let parent = get_int_field j "parent_ID" in
    let node_type = get_field j "node_type" in
    let name = get_string_field j "name" in
    let detached = get_bool_field j "detached" in
    New_node (nid, parent, parse_node_type_from_json node_type, name, detached)

  | "Node_change" ->
    let nid = get_int_field j "node_ID" in
    let update = get_field j "update" in
    Node_change (nid, parse_update update)

  | "Remove" ->
    let nid = get_int_field j "node_ID" in
    Remove nid

  | "Initialized" ->
    let infos = get_field j "infos" in
    Initialized (parse_infos infos)

  | "Saved" -> Saved

  | "Message" ->
    let m = get_field j "message" in
    Message (parse_message m)

  | "Dead" ->
    let s = get_string_field j "message" in
    Dead s

  | "Task" ->
    let nid = get_int_field j "node_ID" in
    let s = get_string_field j "task" in
    let l = get_field j "loc_list" in
    let gl = get_field j "goal_loc" in
    let lang = get_string_field j "lang" in
    Task (nid, s, parse_list_loc l, parse_opt_loc gl, lang)

  | "Next_Unproven_Node_Id" ->
    let nid1 = get_int_field j "node_ID1" in
    let nid2 = get_int_field j "node_ID2" in
    Next_Unproven_Node_Id (nid1, nid2)

  | "File_contents" ->
    let f = get_string_field j "file" in
    let s = get_string_field j "content" in
    let f_format = get_string_field j "file_format" in
    let read_only = get_bool_field j "read_only" in
    File_contents(f,s, f_format, read_only)

  | "Source_and_ce" ->
    let s = get_string_field j "content" in
    let l = get_field j "loc_list" in
    let gl = get_field j "goal_loc" in
    let f_format = get_string_field j "file_format" in
    Source_and_ce(s, parse_list_loc l, parse_opt_loc gl, f_format)

  | "Ident_notif_loc" ->
      let loc = parse_loc (get_field j "ident_loc") in
      Ident_notif_loc loc

  | "Saving_needed" ->
      Saving_needed (get_bool_field j "need_saving")

  | s -> raise (NotNotification ("<from parse_notification> " ^ s))

let parse_notification_json j =
  try
    let constr = get_string_field j "notification" in
    parse_notification constr j
  with
  | Not_found -> raise (NotNotification "<from parse_notification_json>")

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
  | _ -> raise (NotNotification "Not list")

let parse_list_request (s: string): ide_request list =
  let json = parse_json_object s in
  match json with
  | List l -> List.map parse_request_json l
  | _ -> raise (NotRequest "Not list")
