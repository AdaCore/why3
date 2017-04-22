open Itp_communication
open Controller_itp
open Call_provers
open Json_base

(* TODO match exceptions and complete some cases *)

let convert_prover_to_json (p: Whyconf.prover) =
  Obj ["prover_name", String p.Whyconf.prover_name;
         "prover_version", String p.Whyconf.prover_version;
         "prover_altern", String p.Whyconf.prover_altern]

let convert_infos (i: global_information) =
  Obj ["provers", Array (List.map (fun x -> String x) i.provers);
         "transformations", Array (List.map (fun x -> String x) i.transformations);
         "strategies", Array (List.map (fun x -> String x) i.strategies);
         "commands", Array (List.map (fun x -> String x) i.commands)]

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
  Obj ["limit_time", Int l.Call_provers.limit_time;
         "limit_mem", Int l.Call_provers.limit_mem;
         "limit_steps", Int l.Call_provers.limit_steps]

let convert_unix_process (ps: Unix.process_status) =
  match ps with
  | Unix.WEXITED _   -> String "WEXITED"
  | Unix.WSIGNALED _ -> String "WSIGNALED"
  | Unix.WSTOPPED _  -> String "WSTOPPED"

let convert_model (m: Model_parser.model) =
  String (Pp.string_of (fun fmt m -> Model_parser.print_model fmt m) m)

(* TODO pr_model should have a different format *)
let convert_proof_result (pr: prover_result) =
  Obj ["pr_answer", convert_prover_answer pr.pr_answer;
         "pr_status", convert_unix_process pr.pr_status;
         "pr_output", String pr.pr_output;
         "pr_time", Float pr.pr_time;
         "pr_steps", Int pr.pr_steps;
         "pr_model", convert_model pr.pr_model]

let convert_proof_attempt (pas: proof_attempt_status) =
  match pas with
  | Unedited ->
      Obj ["proof_attempt", String "Unedited"]
  | JustEdited ->
      Obj ["proof_attempt", String "JustEdited"]
  | Interrupted ->
      Obj ["proof_attempt", String "Interrupted"]
  | Scheduled ->
      Obj ["proof_attempt", String "Scheduled"]
  | Running ->
      Obj ["proof_attempt", String "Running"]
  | Done pr ->
      Obj ["proof_attempt", String "Done";
             "prover_result", convert_proof_result pr]
  | Controller_itp.InternalFailure e ->
      Obj ["proof_attempt", String "InternalFailure";
             "exception", String (Pp.string_of Exn_printer.exn_printer e)]
  | Uninstalled p ->
      Obj ["proof_attempt", String "Uninstalled";
             "prover", convert_prover_to_json p]

let convert_update u =
  match u with
  | Proved b ->
      Obj ["update_info", String "Proved";
             "proved", Bool b]
  | Proof_status_change (pas, b, l) ->
      Obj ["update_info", String "Proof_status_change";
             "proof_attempt", convert_proof_attempt pas;
             "obsolete", Bool b;
             "limit", convert_limit l]

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
  | Prove_req _               -> String "Prove_req"
  | Transform_req _           -> String "Transform_req"
  | Strategy_req _            -> String "Strategy_req"
  | Open_session_req _        -> String "Open_session_req"
  | Add_file_req _            -> String "Add_file_req"
  | Save_file_req _           -> String "Save_file_req"
  | Set_max_tasks_req _       -> String "Set_max_tasks_req"
  | Get_file_contents _       -> String "Get_file_contents"
  | Get_task _                -> String "Get_task"
  | Remove_subtree _          -> String "Remove_subtree"
  | Copy_paste _              -> String "Copy_paste"
  | Copy_detached _           -> String "Copy_detached"
  | Get_first_unproven_node _ -> String "Get_first_unproven_node"
  | Get_Session_Tree_req      -> String "Get_Session_Tree_req"
  | Clean_req                 -> String "Clean_req"
  | Save_req                  -> String "Save_req"
  | Reload_req                -> String "Reload_req"
  | Replay_req                -> String "Replay_req"
  | Exit_req                  -> String "Exit_req"
  | Interrupt_req             -> String "Interrupt_req"

let print_request_to_json (r: ide_request): Json_base.value =
  let cc = convert_request_constructor in
  match r with
  | Command_req (nid, s) ->
      Obj ["ide_request", cc r;
           "node_ID", Int nid;
           "command", String s]
  | Prove_req (nid, p, l) ->
      Obj ["ide_request", cc r;
           "node_ID", Int nid;
           "prover", String p;
           "limit", convert_limit l]
  | Transform_req (nid, tr, args) ->
      Obj ["ide_request", cc r;
           "node_ID", Int nid;
           "transformation", String tr;
           "arguments", Array (List.map (fun x -> String x) args)]
  | Strategy_req (nid, str) ->
      Obj ["ide_request", cc r;
           "node_ID", Int nid;
           "strategy", String str]
  | Open_session_req f ->
      Obj ["ide_request", cc r;
           "file", String f]
  | Add_file_req f ->
      Obj ["ide_request", cc r;
           "file", String f]
  | Save_file_req (f,_) ->
      Obj ["ide_request", cc r;
           "file", String f]
  | Set_max_tasks_req n ->
      Obj ["ide_request", cc r;
           "tasks", Int n]
  | Get_task n ->
      Obj ["ide_request", cc r;
           "node_ID", Int n]
  | Get_file_contents s ->
      Obj ["ide_request", cc r;
           "file", String s]
  | Remove_subtree n ->
      Obj ["ide_request", cc r;
           "node_ID", Int n]
  | Copy_paste (from_id, to_id) ->
      Obj ["ide_request", cc r;
           "node_ID", Int from_id;
           "node_ID", Int to_id]
  | Copy_detached from_id ->
      Obj ["ide_request", cc r;
           "node_ID", Int from_id]
  | Get_first_unproven_node id ->
      Obj ["ide_request", cc r;
           "node_ID", Int id]
  | Get_Session_Tree_req ->
      Obj ["ide_request", cc r]
  | Clean_req ->
      Obj ["ide_request", cc r]
  | Save_req ->
      Obj ["ide_request", cc r]
  | Reload_req ->
      Obj ["ide_request", cc r]
  | Replay_req ->
      Obj ["ide_request", cc r]
  | Exit_req ->
      Obj ["ide_request", cc r]
  | Interrupt_req ->
      Obj ["ide_request", cc r]

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

let convert_message (m: message_notification) =
  let cc = convert_constructor_message in
  match m with
  | Proof_error (nid, s) ->
      Obj ["mess_notif", cc m;
           "node_ID", Int nid;
           "error", String s]
  | Transf_error (nid, s) ->
      Obj ["mess_notif", cc m;
           "node_ID", Int nid;
           "error", String s]
  | Strat_error (nid, s) ->
      Obj ["mess_notif", cc m;
           "node_ID", Int nid;
           "error", String s]
  | Replay_Info s ->
      Obj ["mess_notif", cc m;
           "replay_info", String s]
  | Query_Info (nid, s) ->
      Obj ["mess_notif", cc m;
           "node_ID", Int nid;
           "qinfo", String s]
  | Query_Error (nid, s) ->
      Obj ["mess_notif", cc m;
           "node_ID", Int nid;
           "qerror", String s]
  | Help s ->
      Obj ["mess_notif", cc m;
           "qhelp", String s]
  | Information s ->
      Obj ["mess_notif", cc m;
           "information", String s]
  | Task_Monitor (n, k, p) ->
      Obj ["mess_notif", cc m;
           "monitor", Array [Int n; Int k; Int p]]
  | Parse_Or_Type_Error s ->
      Obj ["mess_notif", cc m;
           "error", String s]
  | Error s ->
      Obj ["mess_notif", cc m;
           "error", String s]
  | Open_File_Error s ->
      Obj ["mess_notif", cc m;
           "open_error", String s]
  | File_Saved s ->
      Obj ["mess_notif", cc m;
           "information", String s]

let print_notification_to_json (n: notification): Json_base.value =
  let cc = convert_notification_constructor in
  match n with
  | New_node (nid, parent, node_type, name, detached) ->
      Obj ["notification", cc n;
           "node_ID", Int nid;
           "parent_ID", Int parent;
           "node_type", convert_node_type node_type;
           "name", String name;
           "detached", Bool detached]
  | Node_change (nid, update) ->
      Obj ["notification", cc n;
           "node_ID", Int nid;
           "update", convert_update update]
  | Remove nid ->
      Obj ["notification", cc n;
           "node_ID", Int nid]
  | Next_Unproven_Node_Id (from_id, unproved_id) ->
      Obj ["notification", cc n;
           "node_ID", Int from_id;
           "node_ID", Int unproved_id]
  | Initialized infos ->
      Obj ["notification", cc n;
           "infos", convert_infos infos]
  | Saved ->
      Obj ["notification", cc n]
  | Message m ->
      Obj ["notification", cc n;
           "message", convert_message m]
  | Dead s ->
      Obj ["notification", cc n;
           "message", String s]
  | Task (nid, s) ->
      Obj ["notification", cc n;
           "node_ID", Int nid;
           "task", String s]
  | File_contents (f, s) ->
      Obj ["notification", cc n;
           "file", String f;
           "content", String s]

let print_notification fmt (n: notification) =
  Format.fprintf fmt "%a" Json_base.print (print_notification_to_json n)

let print_request fmt (r: ide_request) =
  Format.fprintf fmt "%a" Json_base.print (print_request_to_json r)

let print_list_notification fmt (nl: notification list) =
  Format.fprintf fmt "%a" (Json_base.list print_notification) nl

let print_list_request fmt (rl: ide_request list) =
  Format.fprintf fmt "%a" (Json_base.list print_request) rl

exception NotProver

let parse_prover_from_json (j: Json_base.value) =
  match j with
  | Obj ["prover_name", String pn;
         "prover_version", String pv;
         "prover_altern", String pa] ->
           {Whyconf.prover_name = pn; prover_version = pv; prover_altern = pa}
  | _ -> raise NotProver

exception NotLimit

let parse_limit_from_json (j: Json_base.value) =
  match j with
  | Obj ["limit_time", Int t;
         "limit_mem", Int m;
         "limit_steps", Int s] ->
           {limit_time = t; limit_mem = m; limit_steps = s}
  | _ -> raise NotLimit

exception NotRequest of string

let parse_request (constr: string) l =
  match constr, l with
  | "Command_req", ["node_ID", Int nid;
                    "command", String s] ->
    Command_req (nid, s)
  | "Prove_req", ["node_ID", Int nid;
                  "prover", String p;
                  "limit", l] ->
    Prove_req (nid, p, parse_limit_from_json l)
  | "Transform_req", ["node_ID", Int nid;
                      "transformation", String tr;
                      "arguments", Array args] ->
    Transform_req (nid, tr,
                   List.map (fun x ->
                     match x with
                     | String t -> t
                     | _ -> raise (NotRequest "")) args)
  | "Strategy_req", ["node_ID", Int nid;
                     "strategy", String str] ->
    Strategy_req (nid, str)
  | "Open_session_req", ["file", String f] ->
    Open_session_req f
  | "Add_file_req", ["file", String f] ->
    Add_file_req f
  | "Set_max_tasks_req", ["tasks", Int n] ->
    Set_max_tasks_req n
  | "Get_task", ["node_ID", Int n] ->
    Get_task n
  | "Remove_subtree", ["node_ID", Int n] ->
    Remove_subtree n
  | "Copy_paste", ["node_ID", Int from_id; "node_ID", Int to_id] ->
    Copy_paste (from_id, to_id)
  | "Copy_detached", ["node_ID", Int n] ->
    Copy_detached n
  | "Get_Session_Tree_req", [] ->
    Get_Session_Tree_req
  | "Clean_req" , [] ->
    Clean_req
  | "Save_req", [] ->
    Save_req
  | "Reload_req", [] ->
    Reload_req
  | "Replay_req", [] ->
    Replay_req
  | "Exit_req", [] ->
    Exit_req
  | _ -> raise (NotRequest "")

let parse_request_json (j: Json_base.value): ide_request =
  match j with
  | Obj (("ide_request", String constr) :: l) ->
      parse_request constr l
  | _ -> let s =Pp.string_of Json_base.print j in
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
  match j with
  | Obj ["pr_answer", pr_answer;
           "pr_status", pr_status_unix;
           "pr_output", String pr_output;
           "pr_time", Float pr_time;
           "pr_steps", Int pr_steps;
           "pr_model", String pr_model] ->
     {pr_answer = parse_prover_answer pr_answer;
      pr_status = parse_unix_process pr_status_unix;
      pr_output = pr_output;
      pr_time = pr_time;
      pr_steps = pr_steps;
      pr_model = Obj.magic pr_model} (* TODO pr_model is a string, should be model *)
  | _ -> raise NotProverResult

exception NotProofAttempt

let parse_proof_attempt j =
  match j with
  | Obj ["proof_attempt", String "Unedited"] ->
      Unedited
  | Obj ["proof_attempt", String "JustEdited"] ->
      JustEdited
  | Obj ["proof_attempt", String "Interrupted"] ->
      Interrupted
  | Obj ["proof_attempt", String "Scheduled"] ->
      Scheduled
  | Obj ["proof_attempt", String "Running"] ->
      Running
  | Obj ["proof_attempt", String "Done";
             "prover_result", pr] ->
       Done (parse_prover_result pr)
  | Obj ["proof_attempt", String "InternalFailure";
             "exception", _e] ->
       raise NotProofAttempt (* TODO *)
  | Obj ["proof_attempt", String "Uninstalled";
             "prover", p] ->
       Uninstalled (parse_prover_from_json p)
  | _ -> raise NotProofAttempt

exception NotUpdate

let parse_update j =
  match j with
  | Obj ["update_info", String "Proved";
           "proved", Bool b] ->
    Proved b
  | Obj ["update_info", String "Proof_status_change";
           "proof_attempt", pas;
           "obsolete", Bool b;
           "limit", l] ->
    Proof_status_change (parse_proof_attempt pas, b, parse_limit_from_json l)
  | _ -> raise NotUpdate

exception NotInfos

let parse_infos j =
  match j with
  | Obj ["provers", Array pr;
           "transformations", Array tr;
           "strategies", Array str;
           "commands", Array com] ->
     {provers = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) pr;
      transformations = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) tr;
      strategies = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) str;
      commands = List.map (fun j -> match j with | String x -> x | _ -> raise NotInfos) com}
  | _ -> raise NotInfos

exception NotMessage

let parse_message constr l =
  match constr, l with
  |  "Proof_error", ["node_ID", Int nid;
                    "error", String s] ->
      Proof_error (nid, s)
  | "Transf_error", ["node_ID", Int nid;
                     "error", String s] ->
      Transf_error (nid, s)
  | "Strat_error", ["node_ID", Int nid;
                    "error", String s] ->
      Strat_error (nid, s)
  | "Replay_Info", ["replay_info", String s] ->
      Replay_Info s
  | "Query_Info", ["node_ID", Int nid;
             "qinfo", String s] ->
       Query_Info (nid, s)
  | "Query_Error", ["node_ID", Int nid;
             "qerror", String s] ->
      Query_Error (nid, s)
  | "Help", ["qhelp", String s] ->
      Help s
  | "Information", ["information", String s] ->
      Information s
  | "Task_Monitor", ["monitor", Array [Int n; Int k; Int p]] ->
      Task_Monitor (n, k, p)
  | "Error", ["error", String s] ->
      Error s
  | "Open_File_Error", ["open_error", String s] ->
      Open_File_Error s
  | _ -> raise NotMessage


let parse_message j =
  match j with
  | Obj (("mess_notif", String constr) :: l) ->
      parse_message constr l
  | _ -> raise NotMessage


exception NotNotification of string

let parse_notification constr l =
  match constr, l with
  | "New_node", ["node_ID", Int nid;
                 "parent_ID", Int parent;
                 "node_type", node_type;
                 "name", String name;
                 "detached", Bool detached] ->
      New_node (nid, parent, parse_node_type_from_json node_type, name, detached)
  | "Node_change", ["node_ID", Int nid;
                    "update", update] ->
      Node_change (nid, parse_update update)
  | "Remove", ["node_ID", Int nid] ->
      Remove nid
  | "Initialized", ["infos", infos] ->
      Initialized (parse_infos infos)
  | "Saved", [] -> Saved
  | "Message", ["message", m] ->
      Message (parse_message m)
  | "Dead", ["message", String s] ->
      Dead s
  | "Task", ["node_ID", Int nid;
             "task", String s] ->
       Task (nid, s)
  | "Next_Unproven_Node_Id", [ "node_ID", Int nid1;
                               "node_ID", Int nid2 ] ->
     Next_Unproven_Node_Id (nid1, nid2)
  | "File_contents", [ "file", String f;
                       "content", String s ] ->
     File_contents(f,s)
  | s, _ -> raise (NotNotification ("<from parse_notification> " ^ s))

let parse_notification_json j =
  match j with
  | Obj (("notification", String constr) :: l) ->
      parse_notification constr l
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
  | Array [Null] -> []
  | Array l -> List.map parse_notification_json l
  | _ -> []

let parse_list_request (s: string): ide_request list =
  let json = parse_json_object s in
  match json with
  | Array l -> List.map parse_request_json l
  | _ -> raise (NotRequest "Not list")
