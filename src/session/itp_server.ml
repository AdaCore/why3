open Format
open Stdlib
open Call_provers
open Session_itp
open Controller_itp
open Server_utils

exception Bad_prover_name of string

(**********************************)
(* list unproven goal and related *)
(**********************************)

(* If the transformation is proved, return acc.
   Else, return the concatenation of the reversed list of unproven
   goals below the transformation and acc *)
let rec unproven_goals_below_tn cont acc tn =
  if tn_proved cont tn then
    acc                         (* we ignore "dead" goals *)
  else
    let sub_tasks = get_sub_tasks cont.controller_session tn in
    List.fold_left (unproven_goals_below_pn cont) acc sub_tasks

(* Same as unproven_goals_below_tn; note that if goal is not proved
   and there is no transformation, goal is returned (else it is not) *)
and unproven_goals_below_pn cont acc goal =
  if pn_proved cont goal then
    acc                         (* we ignore "dead" transformations *)
  else
    match get_transformations cont.controller_session goal with
    | [] -> goal :: acc
    | tns -> List.fold_left (unproven_goals_below_tn cont) acc tns

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_th cont acc th =
  if th_proved cont th then
    acc
  else
    let goals = theory_goals th in
    List.fold_left (unproven_goals_below_pn cont) acc goals

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_file cont file =
  if file_proved cont file then
    []
  else
    let theories = file.file_theories in
    List.fold_left (unproven_goals_below_th cont) [] theories

(* returns the list of unproven goals in the controller session *)
let unproven_goals_in_session cont =
  let files = get_files cont.controller_session in
  Stdlib.Hstr.fold (fun _key file acc ->
      let file_goals = unproven_goals_below_file cont file in
      List.rev_append file_goals acc)
    files []

(* [get_first_unproven_goal_around_pn cont pn]
   returns the `first unproven goal' 'after' [pn]. Precisely:
   (1) it finds the youngest ancestor a of [pn] that is not proved
   (2) it returns the first unproved leaf of a
   it returns None if all ancestors are proved *)
let _get_first_unproven_goal_around_pn cont pn =
  let ses = cont.controller_session in
  let rec look_around pn =
    match get_proof_parent ses pn with
    | Trans tn  ->
      if tn_proved cont tn
      then look_around (get_trans_parent ses tn)
      else unproven_goals_below_tn cont [] tn
    | Theory th ->
      if th_proved cont th then begin
        let parent = (theory_parent ses th) in
        if file_proved cont parent
        then unproven_goals_in_session cont
        else unproven_goals_below_file cont parent
      end else
        unproven_goals_below_th cont [] th
  in
  match look_around pn with
  | [] -> None
  | l -> Some (List.hd (List.rev l))

(****************)
(* Command list *)
(****************)
let commands =
  [
    "list-transforms", "list available transformations", Qnotask list_transforms_query;
    "list-provers", "list available provers", Qnotask list_provers;
(*
    "list-strategies", "list available strategies", list_strategies;
*)
    "print", "<s> print the declaration where s was defined", Qtask print_id;
    "search", "<s> print some declarations where s appear", Qtask search_id;
(*
    "r", "reload the session (test only)", test_reload;
    "rp", "replay", test_replay;
    "s", "save the current session", test_save_session;
    "ng", "go to the next goal", then_print (move_to_goal_ret_p next_node);
    "pg", "go to the prev goal", then_print (move_to_goal_ret_p prev_node);
    "gu", "go to the goal up",  then_print (move_to_goal_ret_p zipper_up);
    "gd", "go to the goal down",  then_print (move_to_goal_ret_p zipper_down);
    "gr", "go to the goal right",  then_print (move_to_goal_ret_p zipper_right);
    "gl", "go to the goal left",  then_print (move_to_goal_ret_p zipper_left)
 *)
  ]

let commands_table = Stdlib.Hstr.create 17
let () =
  List.iter
    (fun (c,_,f) -> Stdlib.Hstr.add commands_table c f)
    commands

(*******************)
(* Strategies list *)
(*******************)
let loaded_strategies = ref []

(****** Exception handling *********)

let print_term s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_term tables fmt t

let print_type s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ty tables fmt t

let print_ts s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ts tables fmt t

let print_ls s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ls tables fmt t

let print_tv s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_tv tables fmt t

let print_vsty s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_forget_vsty tables fmt t

let print_pr s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_pr tables fmt t

let print_pat s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_pat tables fmt t

(* Exception reporting *)

(* TODO remove references to id.id_string in this function *)
let bypass_pretty s id =
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        (print_type s id) t1 (print_type s id) t2
  | Ty.BadTypeArity ({Ty.ts_args = []} as ts, _) ->
      fprintf fmt "Type symbol %a expects no arguments" (print_ts s id) ts
  | Ty.BadTypeArity (ts, app_arg) ->
      let i = List.length ts.Ty.ts_args in
      fprintf fmt "Type symbol %a expects %i argument%s but is applied to %i"
        (print_ts s id) ts i (if i = 1 then "" else "s") app_arg
  | Ty.DuplicateTypeVar tv ->
      fprintf fmt "Type variable %a is used twice" (print_tv s id) tv
  | Ty.UnboundTypeVar tv ->
      fprintf fmt "Unbound type variable: %a" (print_tv s id) tv
  | Ty.UnexpectedProp ->
      fprintf fmt "Unexpected propositional type"
  | Term.BadArity ({Term.ls_args = []} as ls, _) ->
      fprintf fmt "%s %a expects no arguments"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
  | Term.BadArity (ls, app_arg) ->
      let i = List.length ls.Term.ls_args in
      fprintf fmt "%s %a expects %i argument%s but is applied to %i"
        (if ls.Term.ls_value = None then "Predicate" else "Function")
        (print_ls s id) ls i (if i = 1 then "" else "s") app_arg
  | Term.EmptyCase ->
      fprintf fmt "Empty match expression"
  | Term.DuplicateVar vs ->
      fprintf fmt "Variable %a is used twice" (print_vsty s id) vs
  | Term.UncoveredVar vs ->
      fprintf fmt "Variable %a uncovered in \"or\"-pattern" (print_vsty s id) vs
  | Term.FunctionSymbolExpected ls ->
      fprintf fmt "Not a function symbol: %a" (print_ls s id) ls
  | Term.PredicateSymbolExpected ls ->
      fprintf fmt "Not a predicate symbol: %a" (print_ls s id) ls
  | Term.ConstructorExpected ls ->
      fprintf fmt "%s %a is not a constructor"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
  | Term.TermExpected t ->
      fprintf fmt "Not a term: %a" (print_term s id) t
  | Term.FmlaExpected t ->
      fprintf fmt "Not a formula: %a" (print_term s id) t
  | Pattern.ConstructorExpected (ls,ty) ->
      fprintf fmt "%s %a is not a constructor of type %a"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
        (print_type s id) ty
  | Pattern.NonExhaustive pl ->
      fprintf fmt "Pattern not covered by a match:@\n  @[%a@]"
        (print_pat s id) (List.hd pl)
  | Decl.BadConstructor ls ->
      fprintf fmt "Bad constructor: %a" (print_ls s id) ls
  | Decl.BadRecordField ls ->
      fprintf fmt "Not a record field: %a" (print_ls s id) ls
  | Decl.RecordFieldMissing (_cs,ls) ->
      fprintf fmt "Field %a is missing" (print_ls s id) ls
  | Decl.DuplicateRecordField (_cs,ls) ->
      fprintf fmt "Field %a is used twice in the same constructor" (print_ls s id) ls
  | Decl.IllegalTypeAlias ts ->
      fprintf fmt
        "Type symbol %a is a type alias and cannot be declared as algebraic"
        (print_ts s id) ts
  | Decl.NonFoundedTypeDecl ts ->
      fprintf fmt "Cannot construct a value of type %a" (print_ts s id) ts
  | Decl.NonPositiveTypeDecl (_ts, ls, ty) ->
      fprintf fmt "Constructor %a \
          contains a non strictly positive occurrence of type %a"
        (print_ls s id) ls (print_type s id) ty
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed inductive clause %a"
        (print_pr s id) pr
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Inductive clause %a contains \
          a non strictly positive occurrence of symbol %a"
        (print_pr s id) pr (print_ls s id) ls1
  | Decl.BadLogicDecl (ls1,ls2) ->
      fprintf fmt "Ill-formed definition: symbols %a and %a are different"
        (print_ls s id) ls1 (print_ls s id) ls2
  | Decl.UnboundVar vs ->
      fprintf fmt "Unbound variable: %a" (print_vsty s id) vs
  | Decl.ClashIdent id ->
      fprintf fmt "Ident %s is defined twice" id.Ident.id_string
  | Decl.EmptyDecl ->
      fprintf fmt "Empty declaration"
  | Decl.EmptyAlgDecl ts ->
      fprintf fmt "Algebraic type %a has no constructors" (print_ts s id) ts
  | Decl.EmptyIndDecl ls ->
      fprintf fmt "Inductive predicate %a has no constructors" (print_ls s id) ls
  | Decl.KnownIdent id ->
      fprintf fmt "Ident %s is already declared" id.Ident.id_string
  | Decl.UnknownIdent id ->
      fprintf fmt "Ident %s is not yet declared" id.Ident.id_string
  | Decl.RedeclaredIdent id ->
      fprintf fmt "Ident %s is already declared, with a different declaration"
        id.Ident.id_string
  | Decl.NoTerminationProof ls ->
      fprintf fmt "Cannot prove the termination of %a" (print_ls s id) ls
  | _ -> Format.fprintf fmt "Uncaught: %a" Exn_printer.exn_printer exn
  end

let get_exception_message ses id fmt e =
  match e with
  | Controller_itp.Noprogress ->
      Format.fprintf fmt "Transformation made no progress\n"
  | Case.Arg_trans_type (s, ty1, ty2) ->
      Format.fprintf fmt "Error in transformation %s during unification of the following terms:\n %a \n %a"
        s (print_type ses id) ty1 (print_type ses id) ty2
  | Case.Arg_trans_term (s, t1, t2) ->
      Format.fprintf fmt "Error in transformation %s during unification of following two terms:\n %a \n %a" s
        (print_term ses id) t1 (print_term ses id) t2
  | Case.Arg_trans (s) ->
      Format.fprintf fmt "Error in transformation function: %s \n" s
  | Case.Arg_hyp_not_found (s) ->
      Format.fprintf fmt "Following hypothesis was not found: %s \n" s
  | Args_wrapper.Arg_theory_not_found (s) ->
      Format.fprintf fmt "Theory not found: %s" s
  | e ->
      bypass_pretty ses id fmt e




(* Information that the IDE may want to have *)
type prover = string
type transformation = string
type strategy = string


type node_ID = int
let root_node : node_ID = 0


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
  | Proof_error           of node_ID * string
  | Transf_error          of node_ID * string
  | Strat_error           of node_ID * string
  | Replay_Info           of string
  | Query_Info            of node_ID * string
  | Query_Error           of node_ID * string
  | Help                  of string
  | Information           of string
  | Task_Monitor          of int * int * int
  | Error                 of string
  | Open_File_Error       of string

type node_type =
  | NRoot
  | NFile
  | NTheory
  | NTransformation
  | NGoal
  | NProofAttempt

type update_info =
  | Proved of bool
  | Proof_status_change of
      Controller_itp.proof_attempt_status
      * bool   (* obsolete or not *)
      * Call_provers.resource_limit

type notification =
  | New_node     of node_ID * node_ID * node_type * string
  (* Notification of creation of new_node:
     New_node (new_node, parent_node, node_type, name). *)
  | Node_change  of node_ID * update_info
  (* inform that the data of the given node changed *)
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
  | Task         of node_ID * string
  (* the node_ID's task *)

type ide_request =
  | Command_req       of node_ID * string
  | Prove_req         of node_ID * prover * resource_limit
  | Transform_req     of node_ID * transformation * string list
  | Strategy_req      of node_ID * strategy
  | Open_session_req  of string
  | Add_file_req      of string
  | Set_max_tasks_req of int
  | Get_task          of node_ID
  | Get_Session_Tree_req
  | Save_req
  | Reload_req
  | Replay_req
  | Exit_req

(* Debugging functions *)
let print_request fmt r =
  match r with
  | Command_req (_nid, s)           -> fprintf fmt "command \"%s\"" s
  | Prove_req (_nid, prover, _rl)   -> fprintf fmt "prove with %s" prover
  | Transform_req (_nid, tr, _args) -> fprintf fmt "transformation :%s" tr
  | Strategy_req (_nid, st)         -> fprintf fmt "strategy %s" st
  | Open_session_req f              -> fprintf fmt "open session file %s" f
  | Add_file_req f                  -> fprintf fmt "open file %s" f
  | Set_max_tasks_req i             -> fprintf fmt "set max tasks %i" i
  | Get_task _nid                   -> fprintf fmt "get task"
  | Get_Session_Tree_req            -> fprintf fmt "get session tree"
  | Save_req                        -> fprintf fmt "save"
  | Reload_req                      -> fprintf fmt "reload"
  | Replay_req                      -> fprintf fmt "replay"
  | Exit_req                        -> fprintf fmt "exit"

let print_msg fmt m =
  match m with
  | Proof_error (_ids, s)  -> fprintf fmt "proof error %s" s
  | Transf_error (_ids, s) -> fprintf fmt "transf error %s" s
  | Strat_error (_ids, s)  -> fprintf fmt "start error %s" s
  | Replay_Info s          -> fprintf fmt "replay info %s" s
  | Query_Info (_ids, s)   -> fprintf fmt "query info %s" s
  | Query_Error (_ids, s)  -> fprintf fmt "query error %s" s
  | Help _s                -> fprintf fmt "help"
  | Information s          -> fprintf fmt "info %s" s
  | Task_Monitor _         -> fprintf fmt "task montor"
  | Error s                -> fprintf fmt "%s" s
  | Open_File_Error s        -> fprintf fmt "%s" s

let print_notify fmt n =
  match n with
  | Node_change (_ni, _nf)          -> fprintf fmt "node change"
  | New_node (ni, _pni, _nt,  _nf) -> fprintf fmt "new node %d" ni
  | Remove _ni                      -> fprintf fmt "remove"
  | Initialized _gi                 -> fprintf fmt "initialized"
  | Saved                           -> fprintf fmt "saved"
  | Message msg                     ->
      print_msg fmt msg
  | Dead s                          -> fprintf fmt "dead :%s" s
  | Task (_ni, _s)                  -> fprintf fmt "task"

module type Protocol = sig
  val get_requests : unit -> ide_request list
  val notify : notification -> unit
end

module Make (S:Controller_itp.Scheduler) (P:Protocol) = struct

  module C = Controller_itp.Make(S)

  let _debug = Debug.register_flag "itp_server"

  (************************)
  (* parsing command line *)
  (************************)

  (* Files are passed with request Open *)
  let config, base_config, env =
    let c, b, e = Whyconf.Args.init () in
    c, b, e

  let get_configs () = config, base_config

  let task_driver =
    let main = Whyconf.get_main config in
    let d = Filename.concat (Whyconf.datadir main)
        (Filename.concat "drivers" "why3_itp.drv")
    in
    Driver.load_driver env d []

  let provers : Whyconf.config_prover Whyconf.Mprover.t =
    Whyconf.get_provers config

  let get_prover_list (config: Whyconf.config) =
    Mstr.fold (fun x _ acc -> x :: acc) (Whyconf.get_prover_shortcuts config) []

  let prover_list: prover list = get_prover_list config
  let transformation_list: transformation list =
    List.map fst (list_transforms ())
  let strategies_list: strategy list =
    let l = strategies env config loaded_strategies in
    List.map (fun (a,_,_,_) -> a) l

  let infos =
    {
     provers = prover_list;
     transformations = transformation_list;
     strategies = strategies_list;
     commands =
       List.map (fun (c,_,_) -> c) commands
    }

  (* Create_controller creates a dummy controller *)
  let cont =
    try
      create_controller env provers
    with LoadDriverFailure (p, e) -> P.notify (Message (
      Error "To implement: could not load driver"));
      raise (LoadDriverFailure (p, e)) (* TODO *)

  (* ------------ init controller ------------ *)

  (* Init cont on file or directory. It is called only when an
     Open_session_req is requested *)
  let init_cont f =
    try (
      if (Sys.file_exists f) then
      begin
        if (Sys.is_directory f) then
        begin
          cont_from_session_dir cont f;
          P.notify (Initialized infos)
        end
        else
        begin
          cont_from_file cont f;
          P.notify (Initialized infos)
        end
      end
      else
        P.notify (Message (Open_File_Error ("Not a file: " ^ f))))
    with
      | NotADirectory f ->
          P.notify (Message (Open_File_Error ("Not a directory: " ^ f)))
      | BadFileName f ->
          P.notify (Message (Open_File_Error ("Bad file name: " ^ f)))
      | e ->
          Format.eprintf "%a@." Exn_printer.exn_printer e;
          P.notify (Dead (Pp.string_of Exn_printer.exn_printer e));
          exit 1

  (* -----------------------------------   ------------------------------------- *)

  let get_node_type (node: any) =
    match node with
    | AFile _ -> NFile
    | ATh _ -> NTheory
    | ATn _ -> NTransformation
    | APn _ -> NGoal
    | APa _ -> NProofAttempt

  let get_node_name (node: any) =
    match node with
    | AFile file ->
      file.file_name
    | ATh th ->
      (theory_name th).Ident.id_string
    | ATn tn ->
      get_transf_name cont.controller_session tn
    | APn pn ->
      (get_proof_name cont.controller_session pn).Ident.id_string
    | APa pa ->
      let pa = get_proof_attempt_node cont.controller_session pa in
      Pp.string_of Whyconf.print_prover pa.prover

(*
  let get_node_proved (node: any) =
    match node with
    | Afile file ->
      file_proved cont file
    | ATh th ->
      th_proved cont th

  let get_info_and_type ses (node: any) =
    match node with
    | AFile file ->
        let name = file.file_name in
        let proved = file_proved cont file in
        NFile, {name; proved}
    | ATh th     ->
        let name = (theory_name th).Ident.id_string in
        let proved = th_proved cont th in
        NTheory, {name; proved}
    | ATn tn     ->
        let name = get_transf_name ses tn in
        let proved = tn_proved cont tn in
        NTransformation, {name; proved}
    | APn pn     ->
        let name = (get_proof_name ses pn).Ident.id_string in
        let proved = pn_proved cont pn in
          NGoal, {name; proved}
    | APa pan    ->
        let pa = get_proof_attempt_node ses pan in
        let name = Pp.string_of Whyconf.print_prover pa.prover in
        let pr, proved = match pa.Session_itp.proof_state with
        | Some pr -> Some pr.pr_answer, pr.pr_answer = Valid
        | None -> None, false
        in
        (NProofAttempt (pr, pa.proof_obsolete)),
        {name; proved}
*)

(* fresh gives new fresh "names" for node_ID using a counter.
   reset resets the counter so that we can regenerate node_IDs as if session
   was fresh *)
  let reset, fresh =
    let count = ref 0 in
    (fun () ->
      count := 0),
    fun () ->
      count := !count + 1;
      !count

  let model_any : any Hint.t = Hint.create 17

  let any_from_node_ID (nid:node_ID) : any = Hint.find model_any nid

  let pan_to_node_ID  : node_ID Hpan.t = Hpan.create 17
  let pn_to_node_ID   : node_ID Hpn.t = Hpn.create 17
  let tn_to_node_ID   : node_ID Htn.t = Htn.create 17
  let th_to_node_ID   : node_ID Ident.Hid.t = Ident.Hid.create 7
  let file_to_node_ID : node_ID Hstr.t = Hstr.create 3

  let node_ID_from_pan  pan  = Hpan.find pan_to_node_ID pan
  let node_ID_from_pn   pn   = Hpn.find pn_to_node_ID pn
  let node_ID_from_tn   tn   = Htn.find tn_to_node_ID tn
  let node_ID_from_th   th   = Ident.Hid.find th_to_node_ID (theory_name th)
  let node_ID_from_file file = Hstr.find file_to_node_ID (file.file_name)

  let node_ID_from_any  any  =
    match any with
    | AFile file -> node_ID_from_file file
    | ATh th     -> node_ID_from_th th
    | ATn tn     -> node_ID_from_tn tn
    | APn pn     -> node_ID_from_pn pn
    | APa pan    -> node_ID_from_pan pan


  let get_prover p =
    match return_prover p config with
    | None -> raise (Bad_prover_name p)
    | Some c -> c

  let add_node_to_table node new_id =
    match node with
    | AFile file -> Hstr.add file_to_node_ID file.file_name new_id
    | ATh th     -> Ident.Hid.add th_to_node_ID (theory_name th) new_id
    | ATn tn     -> Htn.add tn_to_node_ID tn new_id
    | APn pn     -> Hpn.add pn_to_node_ID pn new_id
    | APa pan    -> Hpan.add pan_to_node_ID pan new_id

  (* Create a new node in the_tree, update the tables and send a
     notification about it *)
  let new_node ~parent node : node_ID =
    let new_id = fresh () in
      Hint.add model_any new_id node;
      let node_type = get_node_type node in
      let node_name = get_node_name node in
      add_node_to_table node new_id;
      P.notify (New_node (new_id, parent, node_type, node_name));
      new_id

  let root = 0

  (****************************)
  (* Iter on the session tree *)
  (****************************)

  (* Iter on the session tree with a function [f parent current] with type
     node_ID -> any -> unit *)
  let iter_subtree_proof_attempt_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    Whyconf.Hprover.iter
      (fun _pa panid -> f ~parent (APa panid))
      (get_proof_attempt_ids cont.controller_session id)

  let rec iter_subtree_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    let ses = cont.controller_session in
    f ~parent (APn id);
    let nid = node_ID_from_pn id in
    List.iter
      (fun trans_id -> iter_subtree_from_trans f nid trans_id)
      (get_transformations ses id);
    iter_subtree_proof_attempt_from_goal f nid id

  and iter_subtree_from_trans
    (f: parent:node_ID -> any -> unit) parent trans_id =
    let ses = cont.controller_session in
    f ~parent (ATn trans_id);
    let nid = node_ID_from_tn trans_id in
    List.iter
      (fun goal_id -> (iter_subtree_from_goal f nid goal_id))
      (get_sub_tasks ses trans_id)

  let iter_subtree_from_theory
    (f: parent:node_ID -> any -> unit) parent theory_id =
    f ~parent (ATh theory_id);
    let nid = node_ID_from_th theory_id in
    List.iter (iter_subtree_from_goal f nid)
               (theory_goals theory_id)

  let iter_subtree_from_file
    (f: parent:node_ID -> any -> unit) parent file =
    f ~parent (AFile file);
    let nid = node_ID_from_file file in
    List.iter (iter_subtree_from_theory f nid)
      file.file_theories

  let iter_the_files (f: parent:node_ID -> any -> unit) parent : unit =
    let ses = cont.controller_session in
    let files = get_files ses in
    Stdlib.Hstr.iter
      (fun _ file ->
        iter_subtree_from_file f parent file)
      files

  (**********************************)
  (* Initialization of session tree *)
  (**********************************)

  let _init_the_tree (): unit =
    let f ~parent node_id = ignore (new_node ~parent node_id) in
    iter_the_files f root

  let init_and_send_subtree_from_trans parent trans_id : unit =
    iter_subtree_from_trans
      (fun ~parent id -> ignore (new_node ~parent id)) parent trans_id

  let init_and_send_file f =
    iter_subtree_from_file (fun ~parent id -> ignore (new_node ~parent id))
      root f

  let init_and_send_the_tree (): unit =
    P.notify (New_node (0, 0, NRoot, "root"));
    iter_the_files (fun ~parent id -> ignore (new_node ~parent id)) root

  let resend_the_tree (): unit =
    let send_node ~parent any =
      let node_id = node_ID_from_any any in
      let node_name = get_node_name any in
      let node_type = get_node_type any in
      P.notify (New_node (node_id, parent, node_type, node_name)) in
    P.notify (New_node (0, 0, NRoot, "root"));
    iter_the_files send_node root

  (* -- send the task -- *)
  let send_task nid =
    match any_from_node_ID nid with
    | APn id ->
      let task = get_task cont.controller_session id in
      let tables = get_tables cont.controller_session id in
      let s = Pp.string_of
          (fun fmt -> Driver.print_task ~cntexample:false task_driver fmt tables)
          task in
      P.notify (Task (nid,s))
    | _ ->
      P.notify (Task (nid, "can not associate a task to a node that is not a goal."))

  (* -------------------- *)

  (* Add a file into the session when (Add_file_req f) is sent *)
  (* Note that f is the path from execution directory to the file and fn is the
     path from the session directory to the file. *)
  let add_file_to_session cont f =
    let fn = Sysutil.relativize_filename
      (Session_itp.get_dir cont.controller_session) f in
    let files = get_files cont.controller_session in
    if (not (Stdlib.Hstr.mem files fn)) then
      if (Sys.file_exists f) then
      begin
        Controller_itp.add_file cont f;
        let file = Stdlib.Hstr.find files fn in
        init_and_send_file file
      end
      else
        P.notify (Message (Open_File_Error ("Not a file: " ^ f)))
    else
      P.notify (Message (Open_File_Error ("File already in session: " ^ fn)))


  (* ----------------- Schedule proof attempt -------------------- *)

  (* Callback of a proof_attempt *)
  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    begin match pa_status with
    | Scheduled ->
      begin
        try
          ignore (node_ID_from_pan panid)
        (* TODO: do we notify here ? *)
        with Not_found ->
          let parent_id = get_proof_attempt_parent ses panid in
          let parent = node_ID_from_pn parent_id in
          ignore (new_node ~parent (APa panid))
      end
    (* | Done pr -> *)
    (*   P.notify (Node_change (node_ID_from_pan panid, Proved true)) *)
                             (*{proved=(pr.pr_answer=Valid); name=""})); *)
      (* TODO: we don't want to resend the name every time, separate
         updatable from the rest *)
    | _  -> () (* TODO ? *)
    end;
    let limit = (get_proof_attempt_node cont.controller_session panid).limit in
    let new_status = Proof_status_change (pa_status, false, limit) in
    P.notify (Node_change (node_ID_from_pan panid, new_status))

  let notify_change_proved x b =
    try (
      let node_ID = node_ID_from_any x in
      P.notify (Node_change (node_ID, Proved b))
     )
    with Not_found -> ()

  let schedule_proof_attempt nid (p: Whyconf.config_prover) limit =
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof cont in
    let goals =
      match any_from_node_ID nid with
      | APn pnid   -> [pnid]
      | APa panid  ->
          let ses = cont.controller_session in
          [get_proof_attempt_parent ses panid]
      | ATn tn     ->
        List.rev (unproven_goals_below_tn cont [] tn)
      | AFile file ->
        List.rev (unproven_goals_below_file cont file)
      | ATh th     ->
        List.rev (unproven_goals_below_th cont [] th)
    in
    List.iter (fun id -> C.schedule_proof_attempt cont id prover
                ~limit ~callback ~notification:notify_change_proved)
      goals

  (* ----------------- Schedule transformation -------------------- *)

  (* Callback of a transformation *)
  let callback_update_tree_transform status =
    match status with
    | TSdone trans_id ->
      let ses = cont.controller_session in
      let id = get_trans_parent ses trans_id in
      let nid = node_ID_from_pn id in
      init_and_send_subtree_from_trans nid trans_id
    | TSfailed (id, e) ->
      let msg =
        Pp.sprintf "%a" (get_exception_message cont.controller_session id) e
      in
      P.notify (Message (Strat_error(node_ID_from_pn id, msg)))
    | _ -> ()

  let rec apply_transform nid t args =
    match any_from_node_ID nid with
    | APn id ->
      let callback = callback_update_tree_transform in
      C.schedule_transformation cont id t args ~callback ~notification:notify_change_proved
    | APa panid ->
      let parent_id = get_proof_attempt_parent cont.controller_session panid in
      let parent = node_ID_from_pn parent_id in
      apply_transform parent t args
    | ATn _ | AFile _ | ATh _ ->
      (* TODO: propagate trans to all subgoals, just the first one, do nothing ... ?  *)
      ()

  (* ----------------- run strategy -------------------- *)

  let run_strategy_on_task nid s =
    match any_from_node_ID nid with
    | APn id ->
      let l = strategies cont.controller_env config loaded_strategies in
      let st = List.filter (fun (_,c,_,_) -> c=s) l in
      begin
        match st with
        | [(n,_,_,st)] ->
          Format.printf "running strategy '%s'@." n;
          let callback sts =
            Format.printf "Strategy status: %a@." print_strategy_status sts
          in
          let callback_pa = callback_update_tree_proof cont in
          let callback_tr st = callback_update_tree_transform st in
          C.run_strategy_on_goal cont id st ~callback_pa ~callback_tr ~callback ~notification:notify_change_proved
        | _ -> Format.printf "Strategy '%s' not found@." s
      end
    | _ -> ()

  (* ----------------- Save session --------------------- *)
  let save_session () =
    Session_itp.save_session cont.controller_session;
    P.notify Saved

  (* ----------------- Reload session ------------------- *)
  let clear_tables () : unit =
    reset ();
    Hint.clear model_any;
    Hpan.clear pan_to_node_ID;
    Hpn.clear pn_to_node_ID;
    Htn.clear tn_to_node_ID;
    Ident.Hid.clear th_to_node_ID;
    Hstr.clear file_to_node_ID

  let reload_session () : unit =
    clear_tables ();
    reload_files cont ~use_shapes:true;
    init_and_send_the_tree ()

  let replay_session () : unit =
    let callback = fun lr ->
      P.notify (Message (Replay_Info (Pp.string_of C.replay_print lr))) in
    (* TODO make replay print *)
    C.replay ~use_steps:false cont ~callback:callback ~remove_obsolete:false

  (* ----------------- treat_request -------------------- *)

  let get_proof_node_id nid =
    try
      match any_from_node_ID nid with
      | APn pn_id -> Some pn_id
      | _ -> None
    with
      Not_found -> None

  let rec treat_request r =
    try (
    match r with
    | Prove_req (nid,p,limit)      ->
      let p = try Some (get_prover p) with
      | Bad_prover_name p -> P.notify (Message (Proof_error (nid, "Bad prover name" ^ p))); None
      in
      begin match p with
      | None -> ()
      | Some p -> schedule_proof_attempt nid p limit
      end
    | Transform_req (nid, t, args) -> apply_transform nid t args
    | Strategy_req (nid, st)       -> run_strategy_on_task nid st
    | Save_req                     -> save_session ()
    | Reload_req                   -> reload_session ();
    | Get_Session_Tree_req         -> resend_the_tree ()
    | Get_task nid                 -> send_task nid
    | Replay_req                   -> replay_session (); resend_the_tree ()
    | Command_req (nid, cmd)       ->
      begin
        let snid = get_proof_node_id nid in
        match (interp commands commands_table config cont snid cmd) with
        | Transform (s, _t, args) -> treat_request (Transform_req (nid, s, args))
        | Query s                 -> P.notify (Message (Query_Info (nid, s)))
        | Prove (p, limit)        -> schedule_proof_attempt nid p limit
        | Strategies st           -> run_strategy_on_task nid st
        | Help_message s          -> P.notify (Message (Help s))
        | QError s                -> P.notify (Message (Query_Error (nid, s)))
        | Other (s, _args)        ->
            P.notify (Message (Information ("Unknown command"^s)))
      end
    | Add_file_req f ->
      add_file_to_session cont f
    | Open_session_req file_or_dir_name      ->
      init_cont file_or_dir_name;
      reload_session ()
    | Set_max_tasks_req i     -> C.set_max_tasks i
    | Exit_req                -> exit 0
     )
    with e -> P.notify (Message (Error (Pp.string_of
      (fun fmt (r,e) -> Format.fprintf fmt
          "There was an unrecoverable error during treatment of request:\n %a\nwith exception: %a"
    print_request r Exn_printer.exn_printer e ) (r, e))))

  let treat_requests () : bool =
    List.iter treat_request (P.get_requests ());
    true

  let update_monitor =
    let tr = ref 0 in
    let sr = ref 0 in
    let rr = ref 0 in
    fun t s r ->
      if (not (t = !tr && s = !sr && r = !rr)) then
        begin
          P.notify (Message (Task_Monitor (t,s,r)));
          tr := t;
          sr := s;
          rr := r
        end

  let _ =
    S.timeout ~ms:100 treat_requests;
    (* S.idle ~prio:1 treat_requests; *)
    C.register_observer update_monitor

end
