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

open Format
open Wstdlib
open Session_itp
open Controller_itp
open Server_utils
open Itp_communication

(**********************************)
(* list unproven goal and related *)
(**********************************)

(* If the transformation is proved, return acc.
   Else, return the concatenation of the reversed list of unproven
   goals below the transformation and acc *)
let rec unproven_goals_below_tn cont acc tn =
  let s = cont.controller_session in
  if tn_proved s tn then
    acc                         (* we ignore "dead" goals *)
  else
    let sub_tasks = get_sub_tasks s tn in
    List.fold_left (unproven_goals_below_pn cont) acc sub_tasks

(* Same as unproven_goals_below_tn; note that if goal is not proved
   and there is no transformation, goal is returned (else it is not) *)
and unproven_goals_below_pn cont acc goal =
  let s = cont.controller_session in
  if pn_proved s goal then
    acc                         (* we ignore "dead" transformations *)
  else
    match get_transformations s goal with
    | [] -> goal :: acc
    | tns -> List.fold_left (unproven_goals_below_tn cont) acc tns

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_th cont acc th =
  let s = cont.controller_session in
  if th_proved s th then
    acc
  else
    let goals = theory_goals th in
    List.fold_left (unproven_goals_below_pn cont) acc goals

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_file cont file =
  let s = cont.controller_session in
  if file_proved s file then
    []
  else
    let theories = file_theories file in
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

(****** Exception handling *********)

let p s id =
  let _,tables = Session_itp.get_task_name_table s id in
  (* We use snapshots of printers to avoid registering new values inside it
     only for exception messages.
  *)
  let pr = Ident.duplicate_ident_printer tables.Trans.printer in
  let apr = Ident.duplicate_ident_printer tables.Trans.aprinter in
  (Pretty.create pr apr pr pr false)

let print_opt_type ~print_type fmt t =
  match t with
  | None -> Format.fprintf fmt "bool"
  | Some t -> print_type fmt t

(* Exception reporting *)

(* TODO remove references to id.id_string in this function *)
let bypass_pretty s id =
  let module P = (val (p s id)) in
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        P.print_ty t1 P.print_ty t2
  | Ty.BadTypeArity ({Ty.ts_args = []} as ts, _) ->
      fprintf fmt "Type symbol %a expects no arguments" P.print_ts ts
  | Ty.BadTypeArity (ts, app_arg) ->
      let i = List.length ts.Ty.ts_args in
      fprintf fmt "Type symbol %a expects %i argument%s but is applied to %i"
        P.print_ts ts i (if i = 1 then "" else "s") app_arg
  | Ty.DuplicateTypeVar tv ->
      fprintf fmt "Type variable %a is used twice" P.print_tv tv
  | Ty.UnboundTypeVar tv ->
      fprintf fmt "Unbound type variable: %a" P.print_tv tv
  | Ty.UnexpectedProp ->
      fprintf fmt "Unexpected propositional type"
  | Term.BadArity ({Term.ls_args = []} as ls, _) ->
      fprintf fmt "%s %a expects no arguments"
        (if ls.Term.ls_value = None then "Predicate" else "Function") P.print_ls ls
  | Term.BadArity (ls, app_arg) ->
      let i = List.length ls.Term.ls_args in
      fprintf fmt "%s %a expects %i argument%s but is applied to %i"
        (if ls.Term.ls_value = None then "Predicate" else "Function")
        P.print_ls ls i (if i = 1 then "" else "s") app_arg
  | Term.EmptyCase ->
      fprintf fmt "Empty match expression"
  | Term.DuplicateVar vs ->
      fprintf fmt "Variable %a is used twice" P.print_vsty vs
  | Term.UncoveredVar vs ->
      fprintf fmt "Variable %a uncovered in \"or\"-pattern" P.print_vsty vs
  | Term.FunctionSymbolExpected ls ->
      fprintf fmt "Not a function symbol: %a" P.print_ls ls
  | Term.PredicateSymbolExpected ls ->
      fprintf fmt "Not a predicate symbol: %a" P.print_ls ls
  | Term.ConstructorExpected ls ->
      fprintf fmt "%s %a is not a constructor"
        (if ls.Term.ls_value = None then "Predicate" else "Function") P.print_ls ls
  | Term.TermExpected t ->
      fprintf fmt "Not a term: %a" P.print_term t
  | Term.FmlaExpected t ->
      fprintf fmt "Not a formula: %a" P.print_term t
  | Pattern.ConstructorExpected (ls,ty) ->
      fprintf fmt "%s %a is not a constructor of type %a"
        (if ls.Term.ls_value = None then "Predicate" else "Function") P.print_ls ls
        P.print_ty ty
  | Pattern.NonExhaustive pl ->
      fprintf fmt "Pattern not covered by a match:@\n  @[%a@]"
        P.print_pat (List.hd pl)
  | Decl.BadConstructor ls ->
      fprintf fmt "Bad constructor: %a" P.print_ls ls
  | Decl.BadRecordField ls ->
      fprintf fmt "Not a record field: %a" P.print_ls ls
  | Decl.RecordFieldMissing ls ->
      fprintf fmt "Field %a is missing" P.print_ls ls
  | Decl.DuplicateRecordField ls ->
      fprintf fmt "Field %a is used twice in the same constructor" P.print_ls ls
  | Decl.IllegalTypeAlias ts ->
      fprintf fmt
        "Type symbol %a is a type alias and cannot be declared as algebraic"
        P.print_ts ts
  | Decl.NonFoundedTypeDecl ts ->
      fprintf fmt "Cannot construct a value of type %a" P.print_ts ts
  | Decl.NonPositiveTypeDecl (_ts, ls, ty) ->
      fprintf fmt "Constructor %a \
          contains a non strictly positive occurrence of type %a"
        P.print_ls ls P.print_ty ty
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed inductive clause %a"
        P.print_pr pr
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Inductive clause %a contains \
          a non strictly positive occurrence of symbol %a"
        P.print_pr pr P.print_ls ls1
  | Decl.BadLogicDecl (ls1,ls2) ->
      fprintf fmt "Ill-formed definition: symbols %a and %a are different"
        P.print_ls ls1 P.print_ls ls2
  | Decl.UnboundVar vs ->
      fprintf fmt "Unbound variable:\n%a" P.print_vsty vs
  | Decl.ClashIdent id ->
      fprintf fmt "Ident %s is defined twice" id.Ident.id_string
  | Decl.EmptyDecl ->
      fprintf fmt "Empty declaration"
  | Decl.EmptyAlgDecl ts ->
      fprintf fmt "Algebraic type %a has no constructors" P.print_ts ts
  | Decl.EmptyIndDecl ls ->
      fprintf fmt "Inductive predicate %a has no constructors" P.print_ls ls
  | Decl.KnownIdent id ->
      fprintf fmt "Ident %s is already declared" id.Ident.id_string
  | Decl.UnknownIdent id ->
      fprintf fmt "Ident %s is not yet declared" id.Ident.id_string
  | Decl.RedeclaredIdent id ->
      fprintf fmt "Ident %s is already declared, with a different declaration"
        id.Ident.id_string
  | Decl.NoTerminationProof ls ->
      fprintf fmt "Cannot prove the termination of %a" P.print_ls ls
  | _ -> Format.fprintf fmt "Uncaught: %a" Exn_printer.exn_printer exn
  end

let get_exception_message ses id e =
  let module P = (val (p ses id)) in
  match e with
  | Session_itp.NoProgress ->
      Pp.sprintf "Transformation made no progress\n", Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans s ->
      Pp.sprintf "Error in transformation function: %s \n" s, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_decl (s, ld) ->
      Pp.sprintf "Error in transformation %s during inclusion of following declarations:\n%a" s
        (Pp.print_list (fun fmt () -> Format.fprintf fmt "\n") P.print_tdecl) ld,
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_term (s, t) ->
      Pp.sprintf "Error in transformation %s during with term:\n %a : %a " s
        P.print_term t (print_opt_type ~print_type:P.print_ty) t.Term.t_ty,
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_term2 (s, t1, t2) ->
      Pp.sprintf "Error in transformation %s during unification of following two terms:\n %a : %a \n %a : %a" s
        P.print_term t1 (print_opt_type ~print_type:P.print_ty) t1.Term.t_ty
        P.print_term t2 (print_opt_type ~print_type:P.print_ty) t2.Term.t_ty,
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_term3 (s, t1, t2, t3) ->
      Pp.sprintf "Error in transformation %s during unification of following two terms:\n %a : %a \n %a : %a\n\n%a is already matched with %a" s
        P.print_term t1 (print_opt_type ~print_type:P.print_ty) t1.Term.t_ty
        P.print_term t2 (print_opt_type ~print_type:P.print_ty) t2.Term.t_ty
        P.print_term t1 P.print_term t3,
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_pattern (s, pa1, pa2) ->
      Pp.sprintf "Error in transformation %s during unification of the following terms:\n %a \n %a"
        s P.print_pat pa1 P.print_pat pa2, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_type (s, ty1, ty2) ->
      Pp.sprintf "Error in transformation %s during unification of the following types:\n %a \n %a"
        s P.print_ty ty1 P.print_ty ty2, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_missing (s, svs) ->
      Pp.sprintf "Error in transformation function: %s %a\n" s
        (Pp.print_list Pp.space P.print_vs) (Term.Svs.elements svs),
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_bad_hypothesis ("rewrite", _t) ->
      Pp.sprintf "Not a rewrite hypothesis", Loc.dummy_position, ""
  | Generic_arg_trans_utils.Cannot_infer_type s ->
      Pp.sprintf "Error in transformation %s. Cannot infer type of polymorphic element" s, Loc.dummy_position, ""
  | Args_wrapper.Arg_qid_not_found q ->
      Pp.sprintf "Following hypothesis was not found: %a \n" Typing.print_qualid q, Loc.dummy_position, ""
  | Args_wrapper.Arg_pr_not_found pr ->
      Pp.sprintf "Property not found: %a" P.print_pr pr, Loc.dummy_position, ""
  | Args_wrapper.Arg_error s ->
      Pp.sprintf "Transformation raised a general error: %s \n" s, Loc.dummy_position, ""
  | Args_wrapper.Arg_theory_not_found s ->
      Pp.sprintf "Theory not found: %s" s, Loc.dummy_position, ""
  | Args_wrapper.Arg_parse_type_error (loc, arg, e) ->
      Pp.sprintf "Parsing error: %a" Exn_printer.exn_printer e, loc, arg
  | Args_wrapper.Unnecessary_arguments l ->
      Pp.sprintf "First arguments were parsed and typed correctly but the last following are useless:\n%a"
        (Pp.print_list Pp.newline (fun fmt s -> Format.fprintf fmt "%s" s)) l, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Unnecessary_terms l ->
      Pp.sprintf "First arguments were parsed and typed correctly but the last following are useless:\n%a"
        (Pp.print_list Pp.newline
           (fun fmt s -> Format.fprintf fmt "%a" P.print_term s)) l, Loc.dummy_position, ""
  | Args_wrapper.Arg_expected_none s ->
      Pp.sprintf "An argument was expected of type %s, none were given" s, Loc.dummy_position, ""
  | e ->
      (Pp.sprintf "%a" (bypass_pretty ses id) e), Loc.dummy_position, ""


module type Protocol = sig
  val get_requests : unit -> ide_request list
  val notify : notification -> unit
end

module Make (S:Controller_itp.Scheduler) (Pr:Protocol) = struct

module C = Controller_itp.Make(S)

let debug = Debug.register_flag "itp_server" ~desc:"ITP server"

let debug_attrs = Debug.register_info_flag "print_model_attrs"
  ~desc:"Print@ attrs@ of@ identifiers@ and@ expressions@ in prover@ results."

(****************)
(* Command list *)
(****************)

let interrupt_query _cont _args = C.interrupt (); "interrupted"

let commands_table = Hstr.create 17

let register_command c d f = Hstr.add commands_table c (d,f)

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
    "search", "<ids> print the declarations where all <ids> appears",
    Qtask (search_id ~search_both:false);
    "search_all", "<ids> print the declarations where one of <ids> appears",
    Qtask (search_id ~search_both:true);
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
    { (* task_driver : Driver.driver; *)
      cont : Controller_itp.controller;
      send_source: bool;
      (* If true the server is parametered to send source mlw files as
         notifications *)
      global_infos : Itp_communication.global_information;
    }

  let server_data = ref None

  let get_server_data () =
    match !server_data with
    | None ->
       Format.eprintf "get_server_data(): fatal error, server not yet initialized@.";
       exit 1
    | Some x -> x

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

  let any_from_node_ID (nid:node_ID) : any option =
    try Some (Hint.find model_any nid) with
    | Not_found -> None

  let pan_to_node_ID  : node_ID Hpan.t = Hpan.create 17
  let pn_to_node_ID   : node_ID Hpn.t = Hpn.create 17
  let tn_to_node_ID   : node_ID Htn.t = Htn.create 17
  let th_to_node_ID   : node_ID Ident.Hid.t = Ident.Hid.create 7
  let file_to_node_ID : node_ID Hfile.t = Hfile.create 3

  let node_ID_from_pan  pan  = Hpan.find pan_to_node_ID pan
  let node_ID_from_pn   pn   = Hpn.find pn_to_node_ID pn
  let node_ID_from_tn   tn   = Htn.find tn_to_node_ID tn
  let node_ID_from_th   th   = Ident.Hid.find th_to_node_ID (theory_name th)
  let node_ID_from_file file = Hfile.find file_to_node_ID (file_id file)

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
        let nid = Hfile.find file_to_node_ID (file_id file) in
        Hint.remove model_any nid;
        Hfile.remove file_to_node_ID (file_id file)
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

  let add_node_to_table node new_id =
    match node with
    | AFile file -> Hfile.add file_to_node_ID (file_id file) new_id
    | ATh th     -> Ident.Hid.add th_to_node_ID (theory_name th) new_id
    | ATn tn     -> Htn.add tn_to_node_ID tn new_id
    | APn pn     -> Hpn.add pn_to_node_ID pn new_id
    | APa pan    -> Hpan.add pan_to_node_ID pan new_id


(*******************************)
(* Compute color for locations *)
(*******************************)

(* This section is used to get colored source as a function of the task *)

exception No_loc_on_goal

let get_locations (task: Task.task) =
  let list = ref [] in
  let file_cache = Hstr.create 17 in
  let session_dir =
    let d = get_server_data () in
    Session_itp.get_dir d.cont.controller_session in
  let relativize f =
    try Hstr.find file_cache f
    with Not_found ->
      let path = Sysutil.relativize_filename session_dir f in
      (* FIXME: this an abusive use of Sysutil.system_dependent_absolute_path *)
      let g = Sysutil.system_dependent_absolute_path session_dir path in
      Hstr.replace file_cache f g;
      g in
  let color_loc ~color ~loc =
    let (f,l,b,e) = Loc.get loc in
    let loc = Loc.user_position (relativize f) l b e in
    list := (loc, color) :: !list in
  let rec color_locs ~color formula =
    Opt.iter (fun loc -> color_loc ~color ~loc) formula.Term.t_loc;
    Term.t_iter (fun subf -> color_locs ~color subf) formula in
  let rec color_t_locs ~premise f =
    match f.Term.t_node with
    | Term.Tbinop (Term.Timplies,f1,f2) when not premise ->
      color_t_locs ~premise:true f1;
      color_t_locs ~premise:false f2
    | Term.Tbinop (Term.Tand,f1,f2) when premise ->
      color_t_locs ~premise f1;
      color_t_locs ~premise f2
    | Term.Tlet (_,fb) ->
      let _,f1 = Term.t_open_bound fb in
      color_t_locs ~premise f1
    | Term.Tquant (Term.Tforall,fq) when not premise ->
      let _,_,f1 = Term.t_open_quant fq in
      color_t_locs ~premise f1
    | Term.Tnot f1 when premise && f.Term.t_loc = None ->
      color_locs ~color:Neg_premise_color f1
    | _ when premise ->
      color_locs ~color:Premise_color f
    | _ ->
      color_locs ~color:Goal_color f in
  let color_goal = function
    | None ->
      (* This case can happen when after some transformations: for example, in
         an assert, the new goal asserted is not tagged with locations *)
      (* This error is harmless but we want to detect it when debugging. *)
      if Debug.test_flag Debug.stack_trace then
        raise No_loc_on_goal
    | Some loc -> color_loc ~color:Goal_color ~loc in
  let goal_id : Ident.ident = (Task.task_goal task).Decl.pr_name in
  color_goal goal_id.Ident.id_loc;
  let rec scan = function
    | Some
        { Task.task_prev = prev;
          Task.task_decl =
            { Theory.td_node =
                Theory.Decl { Decl.d_node = Decl.Dprop (k, _, f) }}} ->
      begin match k with
      | Decl.Pgoal  -> color_t_locs ~premise:false f
      | Decl.Paxiom -> color_t_locs ~premise:true  f
      | _ -> assert false
      end;
      scan prev
    | Some { Task.task_prev = prev } -> scan prev
    | _ -> () in
  scan task;
  !list

let get_modified_node n =
  match n with
  | Reset_whole_tree -> None
  | New_node (nid, _, _, _, _) -> Some nid
  | Node_change  (nid, _) -> Some nid
  | Remove nid -> Some nid
  | Next_Unproven_Node_Id (_, nid) -> Some nid
  | Initialized _ -> None
  | Saved | Saving_needed _ -> None
  | Message _ -> None
  | Dead _ -> None
  | Task (nid, _, _) -> Some nid
  | File_contents _ -> None
  | Source_and_ce _ -> None


type focus =
  | Unfocused
(* We can focus on several nodes at once *)
  | Focus_on of Session_itp.any list
  | Wait_focus

(* Focus on a node *)
let focused_node = ref Unfocused
let get_focused_label = ref None

let focus_on_loading (f: Task.task -> bool) =
  focused_node := Wait_focus;
  get_focused_label := Some f

(* TODO *)
module P = struct

  let get_requests = Pr.get_requests

  (* true if nid is below f_node or does not exists (in which case the
     notification is a remove). false if not below.  *)
  let is_below s nid f_nodes =
    let any = any_from_node_ID nid in
    match any with
    | None -> true
    | Some any ->
        List.exists (Session_itp.is_below s any) f_nodes

  let notify n =
    let d = get_server_data() in
    let s = d.cont.controller_session in
    match n with
    | Initialized _ | Saved | Message _ | Dead _ -> Pr.notify n
    | _ ->
      begin
        match !focused_node with
        | Wait_focus -> () (* Do not notify at all *)
        | Unfocused -> Pr.notify n
        | Focus_on f_nodes ->
            let updated_node = get_modified_node n in
            match updated_node with
            | None -> Pr.notify n
            | Some nid when is_below s nid f_nodes ->
                Pr.notify n
            | _ -> ()
      end

end

  (*********************)
  (* File input/output *)
  (*********************)

  let read_and_send f =
    try
      let d = get_server_data() in
      if d.send_source then
(*
        let fn = Sysutil.absolutize_path
            (Session_itp.get_dir d.cont.controller_session) f in
 *)
        let s = Sysutil.file_contents f in
        P.notify (File_contents (f, s))
    with Invalid_argument s ->
      P.notify (Message (Error s))

  let save_file f file_content =
    try
(*
      let d = get_server_data() in
      let fn = Sysutil.absolutize_filename
                 (Session_itp.get_dir d.cont.controller_session) f in
 *)
      Sysutil.backup_file f;
      Sysutil.write_file f file_content;
      P.notify (Message (File_Saved f))
    with Invalid_argument s ->
      P.notify (Message (Error s))

  let relativize_location s loc =
    let f, l, b, e = Loc.get loc in
    let path = Sysutil.relativize_filename (Session_itp.get_dir s) f in
    (* FIXME: this an abusive use of Sysutil.system_dependent_absolute_path *)
    let f = Sysutil.system_dependent_absolute_path "" path in
    Loc.user_position f l b e

  let capture_parse_or_type_errors f cont =
    List.map
      (function
        | Loc.Located (loc, e) ->
           let rel_loc = relativize_location cont.controller_session loc in
           let s = Format.asprintf "%a: %a" Loc.gen_report_position rel_loc
                                   Exn_printer.exn_printer e in
           (loc, rel_loc, s)
        | e when not (Debug.test_flag Debug.stack_trace) ->
           let s = Format.asprintf "%a" Exn_printer.exn_printer e in
           (Loc.dummy_position, Loc.dummy_position, s)
        | e -> raise e)
      (f cont)

  (* Reload_files that is used even if the controller is not correct. It can
     be incorrect and end up in a correct state. *)
  let reload_files cont ~shape_version =
    capture_parse_or_type_errors
      (fun c ->
        try let (_,_) = reload_files ~shape_version c in [] with
        | Errors_list le -> le) cont

  let add_file cont ?format fname =
    capture_parse_or_type_errors
      (fun c ->
        try add_file c ?format fname; [] with
        | Errors_list le -> le) cont


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
    | AFile file -> Session_itp.basename (file_path file)
    | ATh th -> (theory_name th).Ident.id_string
    | ATn tn ->
       let name = get_transf_name d.cont.controller_session tn in
       let args = get_transf_args d.cont.controller_session tn in
       let full = String.concat " " (name :: args) in
       if String.length full >= 40 then
         String.sub full 0 40 ^ " ..."
       else full
    | APn pn ->
       let name = (get_proof_name d.cont.controller_session pn).Ident.id_string in
       (* Reduce the name of the goal to the minimum, by taking the
          part after the last dot: "0" instead of "WP_Parameter.0" for
          example.  *)
       let name = List.hd (Strings.rev_split '.' name) in
       let expl = get_proof_expl d.cont.controller_session pn in
       if expl = "" then name else name ^ " [" ^ expl ^ "]"
    | APa pa ->
      let pa = get_proof_attempt_node d.cont.controller_session pa in
      Pp.string_of Whyconf.print_prover pa.prover

  let get_node_detached (node: any) =
    let d = get_server_data () in
    is_detached d.cont.controller_session node

  let get_node_proved new_id (node: any) =
    let d = get_server_data () in
    let cont = d.cont in
    let s = cont.controller_session in
    match node with
    | AFile file ->
      P.notify (Node_change (new_id, Proved (file_proved s file)))
    | ATh th ->
      P.notify (Node_change (new_id, Proved (th_proved s th)))
    | ATn tn ->
      P.notify (Node_change (new_id, Proved (tn_proved s tn)))
    | APn pn ->
      P.notify (Node_change (new_id, Proved (pn_proved s pn)))
    | APa pa ->
      let pa = get_proof_attempt_node s pa in
      let obs = pa.proof_obsolete in
      let limit = pa.limit in
      let res =
        match pa.Session_itp.proof_state with
        | Some pa -> Done pa
        | _ -> Undone
      in
      P.notify (Node_change (new_id, Proof_status_change(res, obs, limit)))


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

  let add_focused_node node =
    match !focused_node with
    | Focus_on l -> focused_node := Focus_on (node :: l)
    | _ -> focused_node := Focus_on [node]

  (* Focus on label: this is used to automatically focus on the first task
     having a given property (label_detection) in the session tree. To change
     the property, one need to call function register_label_detection. *)
  let focus_on_label node =
    let d = get_server_data () in
    let session = d.cont.Controller_itp.controller_session in
    if not (Session_itp.is_detached session node) then
      match !get_focused_label with
      | Some label_detection ->
          (match node with
          | APn pr_node ->
              let task = Session_itp.get_task session pr_node in
              let b = label_detection task in
              if b then
                add_focused_node node
          | _ -> ())
      | None -> ()

  (* Create a new node in the_tree, update the tables and send a
     notification about it *)
  let new_node ~parent node : node_ID =
    let new_id = fresh () in
      Hint.add model_any new_id node;
      let node_type = get_node_type node in
      let node_name = get_node_name node in
      let node_detached = get_node_detached node in
      add_node_to_table node new_id;
      (* Specific to auto-focus at initialization of itp_server *)
      focus_on_label node;
      begin
        (* Do not send theories that do not contain any goal *)
        match node with
        | ATh th when theory_goals th = [] -> ()
        | _ ->
            P.notify (New_node (new_id, parent, node_type, node_name, node_detached));
            get_node_proved new_id node
      end;
      new_id

  (* Same as new_node but do not return the node. *)
  let create_node ~parent node =
    let _: node_ID = new_node ~parent node in ()

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

  let iter_subtree_from_file (f: parent:node_ID -> any -> unit) file =
    f ~parent:root_node (AFile file);
    let nid = node_ID_from_file file in
    List.iter (iter_subtree_from_theory f nid) (file_theories file)

  let iter_on_files ~(on_file: file -> unit)
                    ~(on_subtree: parent:node_ID -> any -> unit) : unit =
    let d = get_server_data () in
    let ses = d.cont.controller_session in
    let files = get_files ses in
    Hfile.iter
      (fun _ file ->
       on_file file;
       iter_subtree_from_file on_subtree file)
      files

  (**********************************)
  (* Initialization of session tree *)
  (**********************************)


  let send_new_subtree_from_trans parent trans_id : unit =
    iter_subtree_from_trans
      create_node parent trans_id

  let send_new_subtree_from_file f =
    iter_subtree_from_file create_node f

  let reset_and_send_the_whole_tree (): unit =
    P.notify Reset_whole_tree;
    let d = get_server_data () in
    let ses = d.cont.controller_session in
    let on_file f =
      read_and_send (Session_itp.system_path ses f)
    in
    iter_on_files ~on_file ~on_subtree:create_node

  let unfocus () =
    focused_node := Unfocused;
    reset_and_send_the_whole_tree ()

  (* -- send the task -- *)
  let task_of_id d id show_full_context loc =
    let task,tables = get_task_name_table d.cont.controller_session id in
    (* This function also send source locations associated to the task *)
    let loc_color_list = if loc then get_locations task else [] in
    let task_text =
      let pr = tables.Trans.printer in
      let apr = tables.Trans.aprinter in
      let module P = (val Pretty.create pr apr pr pr false) in
      Pp.string_of (if show_full_context then P.print_task else P.print_sequent) task
    in
    task_text, loc_color_list

  let create_ce_tab ~print_attrs s res any list_loc =
    let f = get_encapsulating_file s any in
    let filename = Session_itp.system_path s f in
    let source_code = Sysutil.file_contents filename in
    Model_parser.interleave_with_source ~print_attrs ?start_comment:None ?end_comment:None
      ?me_name_trans:None res.Call_provers.pr_model ~rel_filename:filename
      ~source_code:source_code ~locations:list_loc

  let send_task nid show_full_context loc =
    let d = get_server_data () in
    let any = any_from_node_ID nid in
    match any with
    | None ->
      P.notify (Message (Error "Please select a node id"))
    | Some any ->
    if Session_itp.is_detached d.cont.controller_session any then
      match any with
      | APn _id ->
        let s = "Goal is detached and cannot be printed" in
        P.notify (Task (nid, s, []))
      | ATh t ->
          P.notify (Task (nid, "Detached theory " ^ (theory_name t).Ident.id_string, []))
      | APa pid ->
          let pa = get_proof_attempt_node  d.cont.controller_session pid in
          let name = Pp.string_of Whyconf.print_prover pa.prover in
          let prover_text = "Detached prover\n====================> Prover: " ^ name ^ "\n" in
          P.notify (Task (nid, prover_text, []))
      | AFile f ->
          P.notify (Task (nid, "Detached file " ^ (basename (file_path f)), []))
      | ATn tid ->
          let name = get_transf_name d.cont.controller_session tid in
          let args = get_transf_args d.cont.controller_session tid in
          P.notify (Task (nid, "Detached transformation\n====================> Transformation: " ^
                          String.concat " " (name :: args) ^ "\n", []))
    else
      match any with
      | APn id ->
          let s, list_loc = task_of_id d id show_full_context loc in
          P.notify (Task (nid, s, list_loc))
      | ATh t ->
          P.notify (Task (nid, "Theory " ^ (theory_name t).Ident.id_string, []))
      | APa pid ->
          let print_attrs = Debug.test_flag debug_attrs in
          let pa = get_proof_attempt_node  d.cont.controller_session pid in
          let parid = pa.parent in
          let name = Pp.string_of Whyconf.print_prover pa.prover in
          let s, old_list_loc = task_of_id d parid show_full_context loc in
          let prover_text = s ^ "\n====================> Prover: " ^ name ^ "\n" in
          (* Display the result of the prover *)
          begin
            match pa.proof_state with
            | Some res ->
                let result =
                  Pp.string_of Call_provers.print_prover_answer
                    res.Call_provers.pr_answer
                in
                let ce_result =
                  Pp.string_of (Model_parser.print_model_human ~print_attrs ?me_name_trans:None)
                  res.Call_provers.pr_model
                in
                if ce_result = "" then
                  let result_pr =
                    result ^ "\n\n" ^ "The prover did not return counterexamples."
                  in
                  P.notify (Task (nid, prover_text ^ result_pr, old_list_loc))
                else
                  begin
                    let result_pr =
                      result ^ "\n\n" ^ "Counterexample suggested by the prover:\n\n" ^ ce_result
                    in
                    let (source_result, list_loc) =
                      create_ce_tab d.cont.controller_session ~print_attrs res any old_list_loc
                    in
                    P.notify (Source_and_ce (source_result, list_loc));
                    P.notify (Task (nid, prover_text ^ result_pr, old_list_loc))
                  end
            | None -> P.notify (Task (nid, "Result of the prover not available.\n", old_list_loc))
          end
      | AFile f ->
          P.notify (Task (nid, "File " ^ (basename (file_path f)), []))
      | ATn tid ->
          let name = get_transf_name d.cont.controller_session tid in
          let args = get_transf_args d.cont.controller_session tid in
          let parid = get_trans_parent d.cont.controller_session tid in
          let s, list_loc = task_of_id d parid show_full_context loc in
          P.notify (Task (nid, s ^ "\n====================> Transformation: " ^
                          String.concat " " (name :: args) ^ "\n", list_loc))

  (* -------------------- *)

  (* True when session differs from the saved session *)
  let session_needs_saving = ref false

  (* Add a file into the session when (Add_file_req f) is sent *)
  (* Note that f is the path from execution directory to the file and fn is the
     path from the session directory to the file. *)
  let add_file_to_session cont f =
    let dir = get_dir cont.controller_session in
    let fn = Sysutil.relativize_filename dir f in
    try
      let (_ : file) = find_file_from_path cont.controller_session fn in
      P.notify (Message (Information ("File already in session: " ^ f)))
    with Not_found ->
      if (Sys.file_exists f) then
        let l = add_file cont f in
        let file = find_file_from_path cont.controller_session fn in
        send_new_subtree_from_file file;
        read_and_send (Session_itp.system_path cont.controller_session file);
        begin
          match l with
          | [] ->
             session_needs_saving := true;
             P.notify (Message (Information "file added in session"))
          | l ->
             List.iter
               (function
                 | (loc,rel_loc,s) ->
                    P.notify (Message (Parse_Or_Type_Error(loc,rel_loc,s))))
               l
        end
      else
        P.notify (Message (Open_File_Error ("File not found: " ^ f)))

  (* ------------ init server ------------ *)

  let init_server ?(send_source=true) config env f =
    Debug.dprintf debug "loading session %s@." f;
    let ses,shape_version = Session_itp.load_session f in
    Debug.dprintf debug "creating controller@.";
    let c = create_controller config env ses in
    let shortcuts =
      Mstr.fold
        (fun s p acc -> Whyconf.Mprover.add p s acc)
        (Whyconf.get_prover_shortcuts config) Whyconf.Mprover.empty
    in
    let prover_list =
      Whyconf.Mprover.fold
        (fun pr _ acc ->
         let s = try
             Whyconf.Mprover.find pr shortcuts
           with Not_found -> ""
         in
         let n = Pp.sprintf "%a" Whyconf.print_prover pr in
         let p = Pp.sprintf "%a" Whyconf.print_prover_parseable_format pr in
         (s,n,p) :: acc) (Whyconf.get_provers config) []
    in
    load_strategies c;
    let transformation_list = List.map
      (fun (a, b) -> (a, Format.sprintf "@[%(%)@]" b))
      (list_transforms ()) in
    let strategies_list = list_strategies c in
    let infos =
      {
        provers = prover_list;
        transformations = transformation_list;
        strategies = strategies_list;
        commands =
          Hstr.fold (fun c _ acc -> c :: acc) commands_table []
      }
    in
    server_data := Some
                     { cont = c;
                       send_source = send_source;
                       global_infos = infos;
                     };
    Debug.dprintf debug "reloading source files@.";
    let d = get_server_data () in
    let x = reload_files d.cont ~shape_version in
    reset_and_send_the_whole_tree ();
    (* After initial sending, we don't check anymore that there is a need to
           focus on a specific node. *)
    get_focused_label := None;
    match x with
    | [] ->
       P.notify (Message (Information "Session initialized successfully"))
    | l ->
       List.iter
         (function (loc,rel_loc,s) ->
                   P.notify (Message (Parse_Or_Type_Error(loc,rel_loc,s))))
         l


  (* ----------------- Schedule proof attempt -------------------- *)

  exception Return

  (* Callback of a proof_attempt *)
  let callback_update_tree_proof cont panid pa_status =
    let ses = cont.controller_session in
    let node_id =
      try
        node_ID_from_pan panid
      with Not_found ->
        let parent_id = get_proof_attempt_parent ses panid in
        let parent = node_ID_from_pn parent_id in
        new_node ~parent (APa panid)
    in
    try
      begin match pa_status with
            | UpgradeProver _ ->
               let n = get_node_name (APa panid) in
               P.notify (Node_change (node_id, Name_change n))
            | Removed _ -> P.notify (Remove node_id); raise Return
            | Uninstalled _ -> ()
            | Undone | Scheduled | Running
            | Interrupted | Detached | Done _
            | InternalFailure _ -> ()
      end;
      let pa = get_proof_attempt_node ses panid in
      let new_status =
        Proof_status_change (pa_status, pa.proof_obsolete, pa.limit)
      in
      P.notify (Node_change (node_id, new_status))
    with Return -> ()

  let notify_change_proved c x =
    try
      let node_ID = node_ID_from_any x in
      let b = any_proved c.controller_session x in
      P.notify (Node_change (node_ID, Proved b));
      match x with
      | APa pa ->
         let pa = get_proof_attempt_node c.controller_session pa in
         let res = match pa.Session_itp.proof_state with
           | None -> Undone
           | Some r -> Done r
         in
         let obs = pa.proof_obsolete in
         Debug.dprintf debug
                       "[Itp_server.notify_change_proved: obsolete = %b@." obs;
         let limit = pa.limit in
         P.notify (Node_change (node_ID, Proof_status_change(res, obs, limit)))
      | _ -> ()
    with Not_found when not (Debug.test_flag Debug.stack_trace)->
      Format.eprintf "Fatal anomaly in Itp_server.notify_change_proved@.";
      exit 1

  let schedule_proof_attempt nid (p: Whyconf.config_prover) limit =
    let d = get_server_data () in
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof d.cont in
    let any = any_from_node_ID nid in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"))
    | Some any ->
        let unproven_goals = unproven_goals_below_id d.cont any in
        List.iter (fun id -> C.schedule_proof_attempt ?save_to:None d.cont id
            prover ~limit ~callback ~notification:(notify_change_proved d.cont))
          unproven_goals

  let schedule_edition (nid: node_ID) (prover: Whyconf.prover) =
    let d = get_server_data () in
    let callback = callback_update_tree_proof d.cont in
    let any = any_from_node_ID nid in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"));
    | Some any ->
        try
          let id =
            match any with
            | APn id -> id
            | APa panid ->
                get_proof_attempt_parent d.cont.controller_session panid
            | _ -> raise Not_found
          in
          C.schedule_edition d.cont id prover
            ~callback ~notification:(notify_change_proved d.cont)
        with Not_found ->
          P.notify
            (Message
               (Error
                  "for edition you must select a proof attempt node"))

  (* ----------------- Schedule transformation -------------------- *)

  (* Callback of a transformation.
     This contains arguments of the transformation only for pretty printing of
     errors*)
  let callback_update_tree_transform tr args status =
    let d = get_server_data () in
    match status with
    | TSdone trans_id ->
      let ses = d.cont.controller_session in
      let id = get_trans_parent ses trans_id in
      let nid = node_ID_from_pn id in
      send_new_subtree_from_trans nid trans_id
    | TSfailed (_, NoProgress) ->
        P.notify (Message (Information "The transformation made no progress"))
    | TSfailed (id, e) ->
      let doc = try
        Pp.sprintf "%s\n%a" tr Pp.formatted (Trans.lookup_trans_desc tr)
      with | _ -> "" in
      let msg, loc, arg_opt = get_exception_message d.cont.controller_session id e in
      let tr_applied = tr ^ " " ^ (List.fold_left (fun x acc -> x ^ " " ^ acc) "" args) in
      P.notify (Message (Transf_error (false, node_ID_from_pn id, tr_applied, arg_opt, loc, msg, doc)))
    | TSscheduled -> ()
    | TSfatal (id, e) ->
      let doc = try
        Pp.sprintf "%s\n%a" tr Pp.formatted (Trans.lookup_trans_desc tr)
      with | _ -> "" in
      let msg, loc, arg_opt = get_exception_message d.cont.controller_session id e in
      let tr_applied = tr ^ " " ^ (List.fold_left (fun x acc -> x ^ " " ^ acc) "" args) in
      P.notify (Message (Transf_error (true, node_ID_from_pn id, tr_applied, arg_opt, loc, msg, doc)))

  let apply_transform node_id t args =
    let d = get_server_data () in

    let rec apply_transform nid t args =
      match nid with
      | APn id ->
        if Session_itp.is_detached d.cont.controller_session nid then
          P.notify (Message (Information "Transformation cannot apply on detached node"))
        else
          if Session_itp.check_if_already_exists d.cont.controller_session id t args then
            P.notify (Message (Information "Transformation already applied"))
          else
            let callback = callback_update_tree_transform t args in
            C.schedule_transformation d.cont id t args ~callback
              ~notification:(notify_change_proved d.cont)
      | APa panid ->
        let parent_id = get_proof_attempt_parent d.cont.controller_session panid in
        apply_transform (APn parent_id) t args
      | ATn tnid ->
        let child_ids = get_sub_tasks d.cont.controller_session tnid in
        List.iter (fun id -> apply_transform (APn id) t args) child_ids
      | AFile f ->
        let child_ids = file_theories f in
        List.iter (fun id -> apply_transform (ATh id) t args) child_ids
      | ATh th ->
        let child_ids = theory_goals th in
        List.iter (fun id -> apply_transform (APn id) t args) child_ids
    in
    let nid = any_from_node_ID node_id in
    match nid with
    | None -> P.notify (Message (Error "Please select a node id"));
    | Some nid ->
        apply_transform nid t args

  let removed x =
    let nid = node_ID_from_any x in
    remove_any_node_ID x;
    P.notify (Remove nid)


  let schedule_bisection (nid: node_ID) =
    let d = get_server_data () in
    try
      let id =
        match any_from_node_ID nid with
        | Some (APa panid) -> panid
        | _ -> raise Not_found
      in
      let callback_pa = callback_update_tree_proof d.cont in
      let callback_tr tr args st = callback_update_tree_transform tr args st in
      C.bisect_proof_attempt d.cont id
                             ~callback_tr ~callback_pa
                             ~notification:(notify_change_proved d.cont)
                             ~removed
    with Not_found ->
      P.notify
        (Message
           (Information
              "for bisection please select some proof attempt"))
       | C.CannotRunBisectionOn _ ->
          P.notify
            (Message
               (Error
                  "for bisection please select a successful proof attempt"))


  (* ----------------- run strategy -------------------- *)

  let debug_strat = Debug.register_flag "strategy_exec" ~desc:"Trace strategies execution"

  let run_strategy_on_task nid s =
    let d = get_server_data () in
    let any = any_from_node_ID nid in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"));
    | Some any ->
    let unproven_goals = unproven_goals_below_id d.cont any in
    try
      let (n,_,_,st) = Hstr.find d.cont.controller_strategies s in
      Debug.dprintf debug_strat "[strategy_exec] running strategy '%s'@." n;
      let callback sts =
        Debug.dprintf debug_strat "[strategy_exec] strategy status: %a@." print_strategy_status sts
      in
      let callback_pa = callback_update_tree_proof d.cont in
      let callback_tr tr args st = callback_update_tree_transform tr args st in
      List.iter (fun id ->
                 C.run_strategy_on_goal d.cont id st
                    ~callback_pa ~callback_tr ~callback ~notification:(notify_change_proved d.cont))
                unproven_goals
    with
      Not_found ->
      Debug.dprintf debug_strat "[strategy_exec] strategy '%s' not found@." s



  (* ----------------- Clean session -------------------- *)
  let clean nid =
    let d = get_server_data () in
    C.clean d.cont ~removed nid


  let remove_node nid =
    let d = get_server_data () in
    let any = any_from_node_ID nid in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"))
    | Some any ->
    begin
      try
        remove_subtree
          ~notification:(notify_change_proved d.cont)
          ~removed
          d.cont any
      with RemoveError -> (* TODO send an error instead of information *)
        P.notify (Message (Information "Cannot remove attached proof nodes or theories, and proof_attempt that did not yet return"))
    end

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
    Hfile.clear file_to_node_ID

  let reload_session () : unit =
    let d = get_server_data () in
    (* interrupt all running provers and unfocus before reload *)
    C.interrupt ();
    let _old_focus = !focused_node in
    unfocus ();
    clear_tables ();
    let l = reload_files d.cont
                         ~shape_version:(Some Termcode.current_shape_version)
    in
    reset_and_send_the_whole_tree ();
    match l with
    | [] ->
       (* TODO: try to restore the previous focus : focused_node := old_focus; *)
       P.notify (Message (Information "Session refresh successful"))
    | l ->
       List.iter
         (function (loc,rel_loc,s) ->
                   P.notify (Message (Parse_Or_Type_Error(loc,rel_loc,s))))
         l

  let replay ~valid_only nid : unit =
    let d = get_server_data () in
    let callback = callback_update_tree_proof d.cont in
    let final_callback _ lr =
      P.notify (Message (Replay_Info (Pp.string_of C.replay_print lr))) in
    (* TODO make replay print *)
    C.replay ~valid_only ~use_steps:false ~obsolete_only:true d.cont
             ~callback ~notification:(notify_change_proved d.cont) ~final_callback ~any:nid

(*
  let () = register_command "edit" "remove unsuccessful proof attempts that are below proved goals"
    (Qtask (fun cont _table _args ->  schedule_edition (); "Editor called"))
 *)

(* TODO: should this remove the current selected node ?
  let () = register_command
             "remove_node" "removes a proof attempt or a transformation"
             (Qnotask (fun _cont args ->
                       match args with
                       | [x]
                       clean_session (); "Remove node done"))
 *)

  (* ---------------- Mark obsolete ------------------ *)
  let mark_obsolete n =
    let d = get_server_data () in
    C.mark_as_obsolete ~notification:(notify_change_proved d.cont) d.cont n

  (* ----------------- Get counterexampes ------------ *)
  let get_ce nid =
    let d = get_server_data () in
    let session = d.cont.controller_session in
    let config = d.cont.controller_config in
    let any = any_from_node_ID nid in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"))
    | Some (APa panid) ->
      let pan = Session_itp.get_proof_attempt_node session panid in
      let filter_prover =
        Whyconf.mk_filter_prover ~version:pan.prover.Whyconf.prover_version
          ~altern:"counterexamples" pan.prover.Whyconf.prover_name
      in
      begin match Whyconf.filter_one_prover config filter_prover with
      | config_prover ->
        (* nid should still exists when scheduling attempt *)
        let parent_pn = Session_itp.get_proof_attempt_parent session panid in
        let nid' = node_ID_from_pn parent_pn in
        remove_node nid;
        schedule_proof_attempt nid' config_prover pan.limit
      | exception Whyconf.ProverNotFound (_, fp) ->
        let msg = Format.asprintf "Counterexamples alternative for prover does \
                                   not exists: %a"
            Whyconf.print_filter_prover fp
        in
        P.notify (Message (Error msg))
      end
    | _ -> P.notify (Message (Error "Please select a proofattempt"))


  (* ----------------- locate next unproven node -------------------- *)

  let notify_first_unproven_node d ni =
    let s = d.cont.controller_session in
    let any = any_from_node_ID ni in
    match any with
    | None -> P.notify (Message (Error "Please select a node id"))
    | Some any ->
      let unproven_any =
        get_first_unproven_goal_around
          ~always_send:true
          ~proved:(Session_itp.any_proved s)
          ~children:(get_undetached_children_no_pa s)
          ~get_parent:(get_any_parent s)
          ~is_goal:(fun any -> match any with | APn _ -> true | _ -> false)
          ~is_pa:(fun any -> match any with | APa _ -> true | _ -> false)
          any in
      begin
        match unproven_any with
        | None -> () (* If no node is found we don't tell IDE to move *)
        | Some any ->
            P.notify (Next_Unproven_Node_Id (ni, node_ID_from_any any))
      end

   (* Check if a request is valid (does not suppose existence of obsolete node_id) *)
   let request_is_valid r =
     match r with
     | Save_req | Check_need_saving_req | Reload_req
     | Get_file_contents _ | Save_file_req _
     | Interrupt_req | Add_file_req _ | Set_config_param _ | Set_prover_policy _
     | Exit_req | Get_global_infos | Itp_communication.Unfocus_req -> true
     | Get_first_unproven_node ni ->
         Hint.mem model_any ni
     | Remove_subtree nid ->
         Hint.mem model_any nid
     | Copy_paste (from_id, to_id) ->
         Hint.mem model_any from_id && Hint.mem model_any to_id
     | Get_task(nid,_,_) ->
         Hint.mem model_any nid
     | Command_req (nid, _) ->
         if not (Itp_communication.is_root nid) then
           Hint.mem model_any nid
         else
           true

  (* ----------------- treat_request -------------------- *)

  let treat_request d r =
    match r with
    | Get_global_infos ->
       Debug.dprintf debug "sending initialization infos@.";
       P.notify (Initialized d.global_infos)
    | Save_req                     ->
       save_session ();
       session_needs_saving := false
    | Reload_req                   ->
       reload_session ();
       session_needs_saving := true
    | Get_first_unproven_node ni   ->
      notify_first_unproven_node d ni
    | Remove_subtree nid           ->
       remove_node nid;
       session_needs_saving := true
    | Copy_paste (from_id, to_id) ->
       let from_any = any_from_node_ID from_id in
       let to_any = any_from_node_ID to_id in
       begin
        match from_any, to_any with
        | None, _ | _, None ->
          P.notify (Message (Error "Please select a node id"));
        | Some from_any, Some to_any ->
          begin
            try
              C.copy_paste
                ~notification:(notify_change_proved d.cont)
                ~callback_pa:(callback_update_tree_proof d.cont)
                ~callback_tr:(callback_update_tree_transform)
                d.cont from_any to_any;
              session_needs_saving := true
            with C.BadCopyPaste ->
              P.notify (Message (Error "invalid copy"))
          end
       end
    | Get_file_contents f          ->
       read_and_send f
    | Save_file_req (name, text)   ->
       save_file name text
    | Check_need_saving_req ->
       P.notify (Saving_needed !session_needs_saving)
    | Get_task(nid,b,loc)          ->
       send_task nid b loc
    | Interrupt_req                ->
       C.interrupt ()
    | Command_req (nid, cmd)       ->
       let snid = any_from_node_ID nid in
       begin
         match interp commands_table d.cont snid cmd with
         | Transform (s, _t, args) ->
            apply_transform nid s args;
            session_needs_saving := true
         | Query s                 ->
            P.notify (Message (Query_Info (nid, s)))
         | Prove (p, limit)        ->
            schedule_proof_attempt nid p limit;
            session_needs_saving := true
         | Strategies st           ->
             run_strategy_on_task nid st;
             session_needs_saving := true
         | Edit p                  ->
             schedule_edition nid p;
             session_needs_saving := true
         | Get_ce                  ->
             get_ce nid;
             session_needs_saving := true
         | Bisect                  ->
             schedule_bisection nid;
             session_needs_saving := true
         | Replay valid_only       ->
             replay ~valid_only snid;
             session_needs_saving := true
         | Clean                   ->
             clean snid;
             session_needs_saving := true
         | Mark_Obsolete           ->
             mark_obsolete snid;
             session_needs_saving := true
         | Focus_req ->
             let d = get_server_data () in
             let s = d.cont.controller_session in
             let any = any_from_node_ID nid in
             begin match any with
             | None -> P.notify (Message (Error "Please select a node id"))
             | Some any ->
               let focus_on =
                 match any with
                 | APa pa -> APn (Session_itp.get_proof_attempt_parent s pa)
                 | _ -> any
               in
               focused_node := Focus_on [focus_on];
               reset_and_send_the_whole_tree ()
             end
         | Server_utils.Unfocus_req -> unfocus ()
         | Help_message s          -> P.notify (Message (Information s))
         | QError s                -> P.notify (Message (Query_Error (nid, s)))
         | Other (s, _args)        ->
             P.notify (Message (Information ("Unknown command: "^s)))
       end
    | Add_file_req f ->
      add_file_to_session d.cont f
    | Set_config_param(s,i)   ->
       begin
         match s with
         | "max_tasks" -> Controller_itp.set_session_max_tasks i
         | "timelimit" -> Server_utils.set_session_timelimit i
         | "memlimit" -> Server_utils.set_session_memlimit i
         | _ -> P.notify (Message (Error ("Unknown config parameter "^s)))
       end
    | Set_prover_policy(p,u)   ->
       let c = d.cont in
       Controller_itp.set_session_prover_upgrade_policy c p u
    | Unfocus_req             -> unfocus ()
    | Exit_req                -> exit 0

  let treat_request r =
    let d = get_server_data () in
    (* Check that the request does not refer to obsolete node_ids *)
    if not (request_is_valid r) then
      begin
        (* These errors come from the client-server behavior of itp. They cannot
           be completely avoided and could be safely ignored.
           They are ignored if a debug flag is not added.
         *)
        if Debug.test_flag Debug.stack_trace then
          raise Not_found;
        if Debug.test_flag debug then
          P.notify (Message (Error (Pp.string_of
            (fun fmt r -> Format.fprintf fmt
              "The following request refer to obsolete node_ids:\n %a\n"
             Itp_communication.print_request r) r)))
      end
    else
      try treat_request d r
      with
      | C.TransAlreadyExists (name,args) ->
         P.notify
           (Message
              (Error
                 (Pp.sprintf "Transformation %s with arg [%s] already exists"
                             name args)))
      | C.GoalNodeDetached _id ->
        P.notify
           (Message
              (Information
                 ("Transformation cannot apply on detached node")))
      | e when not (Debug.test_flag Debug.stack_trace)->
         P.notify
           (Message
              (Error
                 (Pp.sprintf
                    "There was an unrecoverable error during treatment of request:\n %a\nwith exception: %a"
                    print_request r Exn_printer.exn_printer e)))

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
    S.timeout ~ms:default_delay_ms treat_requests;
    (* S.idle ~prio:1 treat_requests; *)
    C.register_observer update_monitor

end
