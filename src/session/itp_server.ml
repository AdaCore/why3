open Format
open Stdlib
open Session_itp
open Controller_itp
open Server_utils
open Itp_communication

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

let unproven_goals_below_id cont id =
  match id  with
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

(*******************)
(* Strategies list *)
(*******************)
let loaded_strategies = ref []

(****** Exception handling *********)

let print_term s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_term tables fmt t

let print_type s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ty tables fmt t

let print_ts s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ts tables fmt t

let print_ls s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ls tables fmt t

let print_tv s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_tv tables fmt t

let print_vsty s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_forget_vsty tables fmt t

let print_pr s id fmt t =
  let tables = match (Session_itp.get_table s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_pr tables fmt t

let print_pat s id fmt t =
  let tables = match (Session_itp.get_table s id) with
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
  | Args_wrapper.Arg_hyp_not_found (s) ->
      Format.fprintf fmt "Following hypothesis was not found: %s \n" s
  | Args_wrapper.Arg_theory_not_found (s) ->
      Format.fprintf fmt "Theory not found: %s" s
  | e ->
      bypass_pretty ses id fmt e





(* Debugging functions *)
let print_request fmt r =
  match r with
  | Command_req (_nid, s)           -> fprintf fmt "command \"%s\"" s
  | Prove_req (_nid, prover, _rl)   -> fprintf fmt "prove with %s" prover
  | Transform_req (_nid, tr, _args) -> fprintf fmt "transformation :%s" tr
  | Strategy_req (_nid, st)         -> fprintf fmt "strategy %s" st
(*
  | Open_session_req f              -> fprintf fmt "open session file %s" f
*)
  | Add_file_req f                  -> fprintf fmt "open file %s" f
  | Set_max_tasks_req i             -> fprintf fmt "set max tasks %i" i
  | Get_file_contents _f            -> fprintf fmt "get file contents"
  | Get_first_unproven_node _nid    -> fprintf fmt "get first unproven node"
  | Get_task _nid                   -> fprintf fmt "get task"
  | Remove_subtree _nid             -> fprintf fmt "remove subtree"
  | Copy_paste _                    -> fprintf fmt "copy paste"
  | Copy_detached _                 -> fprintf fmt "copy detached"
  | Get_Session_Tree_req            -> fprintf fmt "get session tree"
  | Save_file_req _                 -> fprintf fmt "save file"
  | Mark_obsolete_req _             -> fprintf fmt "mark obsolete"
  | Clean_req                       -> fprintf fmt "clean"
  | Save_req                        -> fprintf fmt "save"
  | Reload_req                      -> fprintf fmt "reload"
  | Replay_req                      -> fprintf fmt "replay"
  | Exit_req                        -> fprintf fmt "exit"
  | Interrupt_req                   -> fprintf fmt "interrupt"

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
  | Parse_Or_Type_Error s  -> fprintf fmt "parse_or_type_error:\n %s" s
  | File_Saved s           -> fprintf fmt "file saved %s" s
  | Error s                -> fprintf fmt "%s" s
  | Open_File_Error s      -> fprintf fmt "%s" s

(* TODO ad hoc printing. Should reuse print_loc. *)
let print_loc fmt (loc: Loc.position) =
  let (f,l,b,e) = Loc.get loc in
   fprintf fmt "File \"%s\", line %d, characters %d-%d" f l b e

let print_list_loc fmt l =
  Pp.print_list
    (fun _fmt () -> ())
    (fun fmt (loc, _c) -> Format.fprintf fmt "(%a, color)" print_loc loc)
    fmt l

let print_notify fmt n =
  match n with
  | Node_change (ni, nf)               ->
      begin
        match nf with
        | Proved b -> fprintf fmt "node change %d Proved %b" ni b
        | Obsolete b -> fprintf fmt "node change %d Obsolete %b" ni b
        | Proof_status_change(st,b,_lim) ->
           fprintf fmt "node change %d Proof_status_change res=%a obsolete=%b limits=<TODO>"
                   ni Controller_itp.print_status st b
      end
  | New_node (ni, _pni, _nt,  _nf, _d) -> fprintf fmt "new node %d" ni
  | Remove _ni                         -> fprintf fmt "remove"
  | Next_Unproven_Node_Id (_ni, _nj)   -> fprintf fmt "next unproven node_id"
  | Initialized _gi                    -> fprintf fmt "initialized"
  | Saved                              -> fprintf fmt "saved"
  | Message msg                        ->
      print_msg fmt msg
  | Dead s                             -> fprintf fmt "dead :%s" s
  | File_contents (_f, _s)             -> fprintf fmt "file contents"
  | Task (ni, _s, list_loc)            ->
      fprintf fmt "task for node_ID %d which contains a list of loc %a"
        ni print_list_loc list_loc

module type Protocol = sig
  val get_requests : unit -> ide_request list
  val notify : notification -> unit
end

module Make (S:Controller_itp.Scheduler) (P:Protocol) = struct

  module C = Controller_itp.Make(S)

let debug = Debug.register_flag "itp_server" ~desc:"ITP server"


(****************)
(* Command list *)
(****************)

let interrupt_query _cont _args = C.interrupt (); "interrupted"

let commands_table = Stdlib.Hstr.create 17

let register_command c d f = Stdlib.Hstr.add commands_table c (d,f)

let () =
  List.iter (fun (c,d,f) -> register_command c d f)
    [
    "interrupt", "interrupt all scheduled or running proof tasks",
    Qnotask interrupt_query;
    "list-transforms", "list available transformations",
    Qnotask list_transforms_query;
    "list-provers", "list available provers",
    Qnotask list_provers;
(*
    "list-strategies", "list available strategies", list_strategies;
*)
    "print", "<id> print the declaration where <id> was defined",
    Qtask print_id;
    "search", "<is> print declarations where <id> appears",
    Qtask search_id;
(*
    "r", "reload the session (test only)", test_reload;
    "s", "save the current session", test_save_session;
    "ng", "go to the next goal", then_print (move_to_goal_ret_p next_node);
    "pg", "go to the prev goal", then_print (move_to_goal_ret_p prev_node);
    "gu", "go to the goal up",  then_print (move_to_goal_ret_p zipper_up);
    "gd", "go to the goal down",  then_print (move_to_goal_ret_p zipper_down);
    "gr", "go to the goal right",  then_print (move_to_goal_ret_p zipper_right);
    "gl", "go to the goal left",  then_print (move_to_goal_ret_p zipper_left)
 *)
  ]

  type server_data =
    { task_driver : Driver.driver;
      cont : Controller_itp.controller;
    }

  let server_data = ref None

  let get_server_data () =
    match !server_data with
    | None ->
       Format.eprintf "[ITP server] not yet initialized@.";
       exit 1
    | Some x -> x

(*******************************)
(* Compute color for locations *)
(*******************************)

(* This section is used to get colored source as a function of the task *)


(* These functions append stuff to a list which will then be passed to the
   Task notification. *)
let color_loc list ~color ~loc =
  let d = get_server_data () in
  let (f,l,b,e) = Loc.get loc in
  let f = Sysutil.relativize_filename
    (Session_itp.get_dir d.cont.controller_session) f in
  let loc = Loc.user_position f l b e in
  list := (loc, color) :: !list

let rec color_locs list ~color formula =
  let b = ref false in
  Opt.iter (fun loc -> color_loc list ~color ~loc; b := true) formula.Term.t_loc;
  Term.t_fold (fun b subf -> color_locs list ~color subf || b) !b formula

let rec color_t_locs list f =
  let premise_tag = function
    | { Term.t_node = Term.Tnot _; t_loc = None } -> Neg_premise_color
    | _ -> Premise_color
  in
  match f.Term.t_node with
    | Term.Tbinop (Term.Timplies,f1,f2) ->
        let b = color_locs list ~color:(premise_tag f1) f1 in
        color_t_locs list f2 || b
    | Term.Tlet (t,fb) ->
        let _,f1 = Term.t_open_bound fb in
        let b = color_locs list ~color:(premise_tag t) t in
        color_t_locs list f1 || b
    | Term.Tquant (Term.Tforall,fq) ->
        let _,_,f1 = Term.t_open_quant fq in
        color_t_locs list f1
    | _ ->
        color_locs list ~color:Goal_color f

exception No_loc_on_goal

let color_goal list loc =
  match loc with
  | None -> raise No_loc_on_goal
  | Some loc -> color_loc list ~color:Goal_color ~loc

let get_locations list (task: Task.task) =
  let goal_id : Ident.ident = (Task.task_goal task).Decl.pr_name in
  color_goal list goal_id.Ident.id_loc;
  match task with
    | Some
        { Task.task_decl =
            { Theory.td_node =
                Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, f)}}} ->
        if not (color_t_locs list f) then
          Opt.iter (fun loc -> color_loc list ~color:Goal_color ~loc) goal_id.Ident.id_loc
    | _ ->
        assert false

let get_locations t =
  let l = ref [] in
  get_locations l t;
  !l

  (*********************)
  (* File input/output *)
  (*********************)

  let read_and_send f =
    try
      let d = get_server_data() in
      let fn = Sysutil.absolutize_filename
          (Session_itp.get_dir d.cont.controller_session) f in
      let s = Sysutil.file_contents fn in
      P.notify (File_contents (f, s))
    with Invalid_argument s ->
      P.notify (Message (Error s))

  let save_file f file_content =
    try
      let d = get_server_data() in
      let fn = Sysutil.absolutize_filename
          (Session_itp.get_dir d.cont.controller_session) f in
      Sysutil.write_file fn file_content;
      P.notify (Message (File_Saved f))
    with Invalid_argument s ->
      P.notify (Message (Error s))

  (* Send source file from the controller to the IDE even if the controller's
     status is not correct *)
  let load_files_session () =
    let d = get_server_data () in
    let s = d.cont.controller_session in
    let files = Session_itp.get_files s in
    Stdlib.Hstr.iter (fun _ f ->
                      Format.eprintf "File : %s@." f.file_name;
                      read_and_send f.file_name) files

  (* Reload_files that is used even if the controller is not correct. It can
     be incorrect and end up in a correct state. *)
  let reload_files cont ~use_shapes =
    try reload_files cont ~use_shapes; true with
    | e ->
      let s = Format.asprintf "%a@." Exn_printer.exn_printer e in
      P.notify (Message (Parse_Or_Type_Error s));
      false

  let add_file c ?format fname =
    try add_file c ?format fname; true with
    | e ->
        let s = Format.asprintf "%a@." Exn_printer.exn_printer e in
        P.notify (Message (Parse_Or_Type_Error s)); false

  let task_driver config env =
    try
      let main = Whyconf.get_main config in
      let d = Filename.concat (Whyconf.datadir main)
                              (Filename.concat "drivers" "why3_itp.drv")
      in
      let d = Driver.load_driver env d [] in
      Debug.dprintf debug "[ITP server] driver for task printing loaded@.";
      d
    with e ->
      Format.eprintf "Fatal error while loading itp driver: %a@." Exn_printer.exn_printer e;
      exit 1

  let get_prover_list (config: Whyconf.config) =
    Mstr.fold (fun x _ acc -> x :: acc) (Whyconf.get_prover_shortcuts config) []

  (* -----------------------------------   ------------------------------------- *)

  let get_node_type (node: any) =
    match node with
    | AFile _ -> NFile
    | ATh _   -> NTheory
    | ATn _   -> NTransformation
    | APn _   -> NGoal
    | APa _   -> NProofAttempt

  let get_node_name (node: any) =
    let d = get_server_data () in
    match node with
    | AFile file ->
      file.file_name
    | ATh th ->
      (theory_name th).Ident.id_string
    | ATn tn ->
       let name = get_transf_name d.cont.controller_session tn in
       let args = get_transf_args d.cont.controller_session tn in
       let full = String.concat " " (name :: args) in
       if String.length full >= 40 then
         String.sub full 0 40 ^ " ..."
       else full
    | APn pn ->
      (get_proof_name d.cont.controller_session pn).Ident.id_string
    | APa pa ->
      let pa = get_proof_attempt_node d.cont.controller_session pa in
      Pp.string_of Whyconf.print_prover pa.prover

  let get_node_detached (node: any) =
    let d = get_server_data () in
    is_detached d.cont.controller_session node

  let get_node_proved new_id (node: any) =
    let d = get_server_data () in
    let cont = d.cont in
    match node with
    | AFile file ->
      P.notify (Node_change (new_id, Proved (file_proved cont file)))
    | ATh th ->
      P.notify (Node_change (new_id, Proved (th_proved cont th)))
    | ATn tn ->
      P.notify (Node_change (new_id, Proved (tn_proved cont tn)))
    | APn pn ->
      P.notify (Node_change (new_id, Proved (pn_proved cont pn)))
    | APa pa ->
      let pa = get_proof_attempt_node cont.controller_session pa in
      let is_obsolete = pa.proof_obsolete in
      let resource_limit = pa.limit in
      begin
        match pa.Session_itp.proof_state with
        | Some pa ->
            P.notify (Node_change (
                       new_id, Proof_status_change
                                (Done pa, is_obsolete, resource_limit)))
        | _ -> ()
      end

(*
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

  let remove_any_node_ID any =
    match any with
    | AFile file ->
        let nid = Hstr.find file_to_node_ID file.file_name in
        Hint.remove model_any nid;
        Hstr.remove file_to_node_ID file.file_name
    | ATh th     ->
        let nid = Ident.Hid.find th_to_node_ID (theory_name th) in
        Hint.remove model_any nid;
        Ident.Hid.remove th_to_node_ID (theory_name th)
    | ATn tn     ->
        let nid = Htn.find tn_to_node_ID tn in
        Hint.remove model_any nid;
        Htn.remove tn_to_node_ID tn
    | APn pn     ->
        let nid = Hpn.find pn_to_node_ID pn in
        Hint.remove model_any nid;
        Hpn.remove pn_to_node_ID pn
    | APa pa     ->
        let nid = Hpan.find pan_to_node_ID pa in
        Hint.remove model_any nid;
        Hpan.remove pan_to_node_ID pa

  let get_prover p =
    let d = get_server_data () in
    match return_prover p d.cont.controller_config with
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
      let node_detached = get_node_detached node in
      add_node_to_table node new_id;
      P.notify (New_node (new_id, parent, node_type, node_name, node_detached));
      if node_type = NFile then
        read_and_send node_name;
      get_node_proved new_id node;
      new_id

  (****************************)
  (* Iter on the session tree *)
  (****************************)

  (* Iter on the session tree with a function [f parent current] with type
     node_ID -> any -> unit *)
  let iter_subtree_proof_attempt_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    let d = get_server_data () in
    Whyconf.Hprover.iter
      (fun _pa panid -> f ~parent (APa panid))
      (get_proof_attempt_ids d.cont.controller_session id)

  let rec iter_subtree_from_goal
    (f: parent:node_ID -> any -> unit) parent id =
    let d = get_server_data () in
    let ses = d.cont.controller_session in
    f ~parent (APn id);
    let nid = node_ID_from_pn id in
    List.iter
      (fun trans_id -> iter_subtree_from_trans f nid trans_id)
      (get_transformations ses id);
    iter_subtree_proof_attempt_from_goal f nid id

  and iter_subtree_from_trans
    (f: parent:node_ID -> any -> unit) parent trans_id =
    let d = get_server_data () in
    let ses = d.cont.controller_session in
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
    let d = get_server_data () in
    let ses = d.cont.controller_session in
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
    iter_the_files f root_node

  let init_and_send_subtree_from_trans parent trans_id : unit =
    iter_subtree_from_trans
      (fun ~parent id -> ignore (new_node ~parent id)) parent trans_id

  let init_and_send_file f =
    iter_subtree_from_file (fun ~parent id -> ignore (new_node ~parent id))
      root_node f

  let init_and_send_the_tree (): unit =
    iter_the_files (fun ~parent id -> ignore (new_node ~parent id)) root_node

  let resend_the_tree (): unit =
    let send_node ~parent any =
      let node_id = node_ID_from_any any in
      let node_name = get_node_name any in
      let node_type = get_node_type any in
      let node_detached = get_node_detached any in
      P.notify (New_node (node_id, parent, node_type, node_name, node_detached));
      get_node_proved node_id any in
    iter_the_files send_node root_node


  (* -- send the task -- *)
  let task_of_id d id =
    let task = get_task d.cont.controller_session id in
    let tables = get_table d.cont.controller_session id in
    (* This function also send source locations associated to the task *)
    let loc_color_list = get_locations task in
    Pp.string_of
      (Driver.print_task ~cntexample:false ?name_table:tables d.task_driver)
      task, loc_color_list

  let send_task nid =
    let d = get_server_data () in
    match any_from_node_ID nid with
    | APn id ->
       let s, list_loc = task_of_id d id in
       P.notify (Task (nid, s, list_loc))
    | ATh t ->
       P.notify (Task (nid, "Theory " ^ (theory_name t).Ident.id_string, []))
    | APa pid ->
       let pa = get_proof_attempt_node  d.cont.controller_session pid in
       let parid = pa.parent in
       let name = Pp.string_of Whyconf.print_prover pa.prover in
       let s, list_loc = task_of_id d parid in
       P.notify (Task (nid,s ^ "\n====================> Prover: " ^ name ^ "\n", list_loc))
    | AFile f ->
       P.notify (Task (nid, "File " ^ f.file_name, []))
    | ATn tid ->
       let name = get_transf_name d.cont.controller_session tid in
       let args = get_transf_args d.cont.controller_session tid in
       let parid = get_trans_parent d.cont.controller_session tid in
       let s, list_loc = task_of_id d parid in
       P.notify (Task (nid, s ^ "\n====================> Transformation: " ^ String.concat " " (name :: args) ^ "\n", list_loc))

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
        let b = add_file cont f in
        if b then
          let file = Stdlib.Hstr.find files fn in
          init_and_send_file file
      end
      else
        P.notify (Message (Open_File_Error ("File not found: " ^ f)))
    else
      P.notify (Message (Open_File_Error ("File already in session: " ^ fn)))


  (* ------------ init server ------------ *)

  let init_server config env f =
    Debug.dprintf debug "[ITP server] loading session %s@." f;
    let ses,use_shapes = Session_itp.load_session f in
    Debug.dprintf debug "[ITP server] creating controller@.";
    let c = create_controller config env ses in
    let task_driver = task_driver config env in
    server_data := Some
                     { task_driver = task_driver;
                       cont = c };
    let d = get_server_data () in
    let prover_list = get_prover_list config in
    let transformation_list = List.map fst (list_transforms ()) in
    let strategies_list =
      let l = strategies d.cont.controller_env config loaded_strategies in
      List.map (fun (a,_,_,_) -> a) l
    in
    let infos =
      {
        provers = prover_list;
        transformations = transformation_list;
        strategies = strategies_list;
        commands =
          Hstr.fold (fun c _ acc -> c :: acc) commands_table []
      }
    in
    Debug.dprintf debug "[ITP server] sending initialization infos@.";
    P.notify (Initialized infos);
    Debug.dprintf debug "[ITP server] reloading source files@.";
    let b = reload_files d.cont ~use_shapes in
    if b then
      init_and_send_the_tree ()
    else
      load_files_session ()


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
    | _  -> () (* TODO ? status like Uninstalled should not generate a Notification *)
    end;
    let limit = (get_proof_attempt_node cont.controller_session panid).limit in
    let new_status = Proof_status_change (pa_status, false, limit) in
    P.notify (Node_change (node_ID_from_pan panid, new_status))

  let notify_change_proved c x =
    try
      let node_ID = node_ID_from_any x in
      let b = any_proved c x in
      P.notify (Node_change (node_ID, Proved b));
      match x with
      | APa pa ->
         let obs = (get_proof_attempt_node c.controller_session pa).proof_obsolete in
         P.notify (Node_change (node_ID, Obsolete obs))
      | _ -> ()
    with Not_found -> ()

  let schedule_proof_attempt ~counterexmp nid (p: Whyconf.config_prover) limit =
    let d = get_server_data () in
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof d.cont in
    let unproven_goals = unproven_goals_below_id d.cont (any_from_node_ID nid) in
    List.iter (fun id -> C.schedule_proof_attempt d.cont id prover ~counterexmp
                ~limit ~callback ~notification:(notify_change_proved d.cont))
      unproven_goals

  (* ----------------- Schedule transformation -------------------- *)

  (* Callback of a transformation *)
  let callback_update_tree_transform status =
    let d = get_server_data () in
    match status with
    | TSdone trans_id ->
      let ses = d.cont.controller_session in
      let id = get_trans_parent ses trans_id in
      let nid = node_ID_from_pn id in
      init_and_send_subtree_from_trans nid trans_id
    | TSfailed (id, e) ->
      let msg =
        Pp.sprintf "%a" (get_exception_message d.cont.controller_session id) e
      in
      P.notify (Message (Transf_error (node_ID_from_pn id, msg)))
    | _ -> ()

  let rec apply_transform nid t args =
    let d = get_server_data () in
    match any_from_node_ID nid with
    | APn id ->
      let callback = callback_update_tree_transform in
      C.schedule_transformation d.cont id t args ~callback ~notification:(notify_change_proved d.cont)
    | APa panid ->
      let parent_id = get_proof_attempt_parent d.cont.controller_session panid in
      let parent = node_ID_from_pn parent_id in
      apply_transform parent t args
    | ATn _ | AFile _ | ATh _ ->
      (* TODO: propagate trans to all subgoals, just the first one, do nothing ... ?  *)
      ()

  (* ----------------- run strategy -------------------- *)

  let debug_strat = Debug.register_flag "strategy_exec" ~desc:"Trace strategies execution"

  let run_strategy_on_task ~counterexmp nid s =
    let d = get_server_data () in
    let unproven_goals = unproven_goals_below_id d.cont (any_from_node_ID nid) in
    let l = strategies d.cont.controller_env d.cont.controller_config loaded_strategies in
    let st = List.filter (fun (_,c,_,_) -> c=s) l in
    match st with
    | [(n,_,_,st)] ->
        Debug.dprintf debug_strat "[strategy_exec] running strategy '%s'@." n;
       let callback sts =
         Debug.dprintf debug_strat "[strategy_exec] strategy status: %a@." print_strategy_status sts
       in
       let callback_pa = callback_update_tree_proof d.cont in
       let callback_tr st = callback_update_tree_transform st in
       List.iter (fun id ->
                  C.run_strategy_on_goal d.cont id st ~counterexmp
                    ~callback_pa ~callback_tr ~callback ~notification:(notify_change_proved d.cont))
                 unproven_goals
    | _ ->  Debug.dprintf debug_strat "[strategy_exec] strategy '%s' not found@." s


  (* ----------------- Clean session -------------------- *)
  let clean_session () =
    let d = get_server_data () in
    let remove x =
      let nid = node_ID_from_any x in
      remove_any_node_ID x;
      P.notify (Remove nid) in
    C.clean_session d.cont ~remove


  (* ----------------- Save session --------------------- *)
  let save_session () =
    let d = get_server_data () in
    Session_itp.save_session d.cont.controller_session;
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
    let d = get_server_data () in
    clear_tables ();
    (* Calling reload_files breaks the controller if it fails *)
    let b = reload_files d.cont ~use_shapes:true in
    if b then init_and_send_the_tree ()


  let replay_session () : unit =
    let d = get_server_data () in
    let callback = callback_update_tree_proof d.cont in
    let final_callback lr =
      P.notify (Message (Replay_Info (Pp.string_of C.replay_print lr))) in
    (* TODO make replay print *)
    C.replay ~use_steps:false ~obsolete_only:true d.cont
             ~callback ~notification:(notify_change_proved d.cont) ~final_callback

  let () = register_command "replay" "replay obsolete proofs"
    (Qnotask (fun _cont _args ->  replay_session (); "replay in progress, be patient"))

  (* ---------------- Mark obsolete ------------------ *)
  let mark_obsolete n =
    let d = get_server_data () in
    let any = any_from_node_ID n in
(*
    let node_obsolete x b =
      let nid = node_ID_from_any x in
      P.notify (Node_change (nid, Obsolete b)) in
 *)
    C.mark_as_obsolete (* ~node_obsolete *) ~notification:(notify_change_proved d.cont) d.cont any

  (* ----------------- locate next unproven node -------------------- *)

  let notify_first_unproven_node d ni =
    let any = any_from_node_ID ni in
      let unproven_any =
        get_first_unproven_goal_around
          ~proved:(Controller_itp.any_proved d.cont)
          ~children:(get_undetached_children_no_pa d.cont.controller_session)
          ~get_parent:(get_any_parent d.cont.controller_session)
          ~is_goal:(fun any -> match any with | APn _ -> true | _ -> false)
          ~is_pa:(fun any -> match any with | APa _ -> true | _ -> false)
          any in
      begin
        match unproven_any with
        | None -> () (* If no node is found we don't tell IDE to move *)
        | Some any ->
            P.notify (Next_Unproven_Node_Id (ni, node_ID_from_any any))
      end


  (* ----------------- treat_request -------------------- *)

  let get_proof_node_id nid =
    try
      match any_from_node_ID nid with
      | APn pn_id -> Some pn_id
      | _ -> None
    with
      Not_found -> None

  let rec treat_request r =
    let d = get_server_data () in
    let config = d.cont.controller_config in
    try (
    match r with
    | Prove_req (nid,p,limit)      ->
      let p = try Some (get_prover p) with
      | Bad_prover_name p -> P.notify (Message (Proof_error (nid, "Bad prover name" ^ p))); None
      in
      begin match p with
      | None -> ()
      | Some p ->
          let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
          schedule_proof_attempt ~counterexmp nid p limit
      end
    | Transform_req (nid, t, args) -> apply_transform nid t args
    | Strategy_req (nid, st)       ->
        let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
        run_strategy_on_task ~counterexmp nid st
    | Clean_req                    -> clean_session ()
    | Save_req                     -> save_session ()
    | Reload_req                   -> reload_session ()
    | Get_Session_Tree_req         -> resend_the_tree ()
    | Get_first_unproven_node ni   ->
      notify_first_unproven_node d ni
    | Remove_subtree nid           ->
        let n = any_from_node_ID nid in
        begin
        try
          Controller_itp.remove_subtree d.cont n
            ~notification:(notify_change_proved d.cont)
            ~removed:(fun x ->
                        let nid = node_ID_from_any x in
                        remove_any_node_ID x;
                        P.notify (Remove nid))
        with RemoveError -> (* TODO send an error instead of information *)
          P.notify (Message (Information "Cannot remove attached proof nodes or theories, and proof_attempt that did not yet return"))
        end
    | Copy_paste (from_id, to_id)    ->
        let from_any = any_from_node_ID from_id in
        let to_any = any_from_node_ID to_id in
        C.copy_paste ~notification:(notify_change_proved d.cont)
          ~callback_pa:(callback_update_tree_proof d.cont)
          ~callback_tr:(callback_update_tree_transform)
          d.cont from_any to_any

    | Copy_detached from_id        ->
        let from_any = any_from_node_ID from_id in
        let copy ~parent p =
          let parent = node_ID_from_any parent in
          ignore (new_node ~parent p)
        in
        C.copy_detached ~copy d.cont from_any
    | Get_file_contents f          ->
        read_and_send f
    | Mark_obsolete_req n          -> mark_obsolete n
    | Save_file_req (name, text)   ->
        save_file name text;
    | Get_task nid                 -> send_task nid
    | Replay_req                   -> replay_session ()
    | Interrupt_req                -> C.interrupt ()
    | Command_req (nid, cmd)       ->
      begin
        let snid = get_proof_node_id nid in
        match (interp commands_table d.cont.controller_config d.cont snid cmd) with
        | Transform (s, _t, args) -> treat_request (Transform_req (nid, s, args))
        | Query s                 -> P.notify (Message (Query_Info (nid, s)))
        | Prove (p, limit)        ->
            let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
            schedule_proof_attempt ~counterexmp nid p limit
        | Strategies st           ->
            let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
            run_strategy_on_task ~counterexmp nid st
        | Help_message s          -> P.notify (Message (Help s))
        | QError s                -> P.notify (Message (Query_Error (nid, s)))
        | Other (s, _args)        ->
            P.notify (Message (Information ("Unknown command: "^s)))
      end
    | Add_file_req f ->
      add_file_to_session d.cont f;
      let f = Sysutil.relativize_filename
          (Session_itp.get_dir d.cont.controller_session) f in
      read_and_send f
(*
    | Open_session_req file_or_dir_name ->
        let b = init_cont file_or_dir_name in
        if b then
          reload_session ()
        else
          () (* Eventually print debug here *)
*)
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
