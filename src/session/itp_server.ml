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

open Format
open Stdlib
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
  let _,tables = Session_itp.get_task s id in
  let pr = tables.Trans.printer in
  let apr = tables.Trans.aprinter in
  (Pretty.create pr apr pr pr false)

let print_term s id fmt t =
  let module P = (val (p s id)) in P.print_term fmt t

let print_type s id fmt t =
  let module P = (val (p s id)) in P.print_ty fmt t

let print_opt_type s id fmt t =
  match t with
  | None -> Format.fprintf fmt "bool"
  | Some t -> print_type s id fmt t

let print_ts s id fmt t =
  let module P = (val (p s id)) in P.print_ts fmt t

let print_ls s id fmt t =
  let module P = (val (p s id)) in P.print_ls fmt t

let print_tv s id fmt t =
  let module P = (val (p s id)) in P.print_tv fmt t

let print_vsty s id fmt t =
  let module P = (val (p s id)) in P.print_vsty fmt t

let print_pr s id fmt t =
  let module P = (val (p s id)) in P.print_pr fmt t

let print_pat s id fmt t =
  let module P = (val (p s id)) in P.print_pat fmt t

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
  | Decl.RecordFieldMissing ls ->
      fprintf fmt "Field %a is missing" (print_ls s id) ls
  | Decl.DuplicateRecordField ls ->
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
      fprintf fmt "Unbound variable:\n%a" (print_vsty s id) vs
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

let get_exception_message ses id e =
  match e with
  | Controller_itp.Noprogress ->
      Pp.sprintf "Transformation made no progress\n", Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans s ->
      Pp.sprintf "Error in transformation function: %s \n" s, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_term (s, t1, t2) ->
      Pp.sprintf "Error in transformation %s during unification of following two terms:\n %a : %a \n %a : %a" s
        (print_term ses id) t1 (print_opt_type ses id) t1.Term.t_ty
        (print_term ses id) t2 (print_opt_type ses id) t2.Term.t_ty,
      Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_pattern (s, pa1, pa2) ->
      Pp.sprintf "Error in transformation %s during unification of the following terms:\n %a \n %a"
        s (print_pat ses id) pa1 (print_pat ses id) pa2, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_trans_type (s, ty1, ty2) ->
      Pp.sprintf "Error in transformation %s during unification of the following types:\n %a \n %a"
        s (print_type ses id) ty1 (print_type ses id) ty2, Loc.dummy_position, ""
  | Generic_arg_trans_utils.Arg_bad_hypothesis ("rewrite", _t) ->
      Pp.sprintf "Not a rewrite hypothesis", Loc.dummy_position, ""
  | Generic_arg_trans_utils.Cannot_infer_type s ->
      Pp.sprintf "Error in transformation %s. Cannot infer type of polymorphic element" s, Loc.dummy_position, ""
  | Args_wrapper.Arg_qid_not_found q ->
      Pp.sprintf "Following hypothesis was not found: %a \n" Typing.print_qualid q, Loc.dummy_position, ""
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
           (fun fmt s -> Format.fprintf fmt "%a" (print_term ses id) s)) l, Loc.dummy_position, ""
  | Args_wrapper.Arg_expected_none s ->
      Pp.sprintf "An argument was expected of type %s, none were given" s, Loc.dummy_position, ""
  | e ->
      (Pp.sprintf "%a" (bypass_pretty ses id) e), Loc.dummy_position, ""


(* Debugging functions *)
let print_request fmt r =
  match r with
  | Command_req (_nid, s)           -> fprintf fmt "command \"%s\"" s
  | Add_file_req f                  -> fprintf fmt "open file %s" f
  | Set_config_param(s,i)           -> fprintf fmt "set config param %s %i" s i
  | Get_file_contents _f            -> fprintf fmt "get file contents"
  | Get_first_unproven_node _nid    -> fprintf fmt "get first unproven node"
  | Get_task(nid,b,c,loc)           -> fprintf fmt "get task(%d,%b,%b,%b)" nid b c loc
  | Focus_req _nid                  -> fprintf fmt "focus"
  | Unfocus_req                     -> fprintf fmt "unfocus"
  | Remove_subtree _nid             -> fprintf fmt "remove subtree"
  | Copy_paste _                    -> fprintf fmt "copy paste"
  | Save_file_req _                 -> fprintf fmt "save file"
  | Save_req                        -> fprintf fmt "save"
  | Reload_req                      -> fprintf fmt "reload"
  | Exit_req                        -> fprintf fmt "exit"
  | Interrupt_req                   -> fprintf fmt "interrupt"

let print_msg fmt m =
  match m with
  | Proof_error (_ids, s)                        -> fprintf fmt "proof error %s" s
  | Transf_error (_ids, _tr, _args, _loc, s, _d) -> fprintf fmt "transf error %s" s
  | Strat_error (_ids, s)                        -> fprintf fmt "start error %s" s
  | Replay_Info s                                -> fprintf fmt "replay info %s" s
  | Query_Info (_ids, s)                         -> fprintf fmt "query info %s" s
  | Query_Error (_ids, s)                        -> fprintf fmt "query error %s" s
  | Help _s                                      -> fprintf fmt "help"
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

let print_list_loc fmt l =
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
  | Remove _ni                         -> fprintf fmt "remove"
  | Next_Unproven_Node_Id (ni, nj)   -> fprintf fmt "next unproven node_id from %d is %d" ni nj
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

module Make (S:Controller_itp.Scheduler) (Pr:Protocol) = struct

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
    "search", "<ids> print the declarations where all <ids> appears",
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
    { (* task_driver : Driver.driver; *)
      cont : Controller_itp.controller;
      send_source: bool;
      (* If true the server is parametered to send source mlw files as
         notifications *)
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
  let node_ID_from_file file = Hstr.find file_to_node_ID (file_name file)

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
        let nid = Hstr.find file_to_node_ID (file_name file) in
        Hint.remove model_any nid;
        Hstr.remove file_to_node_ID (file_name file)
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
    | AFile file -> Hstr.add file_to_node_ID (file_name file) new_id
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
      let g = Sysutil.relativize_filename session_dir f in
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
  | Saved -> None
  | Message _ -> None
  | Dead _ -> None
  | Task (nid, _, _) -> Some nid
  | File_contents _ -> None


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
    let any = try Some (any_from_node_ID nid) with _ -> None in
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
      Sysutil.backup_file fn;
      Sysutil.write_file fn file_content;
      P.notify (Message (File_Saved f))
    with Invalid_argument s ->
      P.notify (Message (Error s))

  let relativize_location s loc =
    let f, l, b, e = Loc.get loc in
    let f = Sysutil.relativize_filename (Session_itp.get_dir s) f in
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
  let reload_files cont ~use_shapes =
    capture_parse_or_type_errors
      (fun c -> let (e,_,_) = reload_files ~use_shapes c in e) cont

  let add_file cont ?format fname =
    capture_parse_or_type_errors
      (fun c ->
       match add_file c ?format fname with
       | None -> []
       | Some e -> [e]) cont


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
    | AFile file -> file_name file
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
    match !get_focused_label with
    | Some label_detection ->
        let d = get_server_data () in
        let session = d.cont.Controller_itp.controller_session in
        (match node with
        | APn pr_node ->
            let task = Session_itp.get_raw_task session pr_node in
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
      P.notify (New_node (new_id, parent, node_type, node_name, node_detached));
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

  let iter_subtree_from_file (f: parent:node_ID -> any -> unit) file =
    f ~parent:root_node (AFile file);
    let nid = node_ID_from_file file in
    List.iter (iter_subtree_from_theory f nid) (file_theories file)

  let iter_on_files ~(on_file: file -> unit)
                    ~(on_subtree: parent:node_ID -> any -> unit) : unit =
    let d = get_server_data () in
    let ses = d.cont.controller_session in
    let files = get_files ses in
    Stdlib.Hstr.iter
      (fun _ file ->
       on_file file;
       iter_subtree_from_file on_subtree file)
      files

  (**********************************)
  (* Initialization of session tree *)
  (**********************************)

(*
  let _init_the_tree (): unit =
    let f ~parent node_id = ignore (new_node ~parent node_id) in
    iter_the_files f root_node
*)

  let send_new_subtree_from_trans parent trans_id : unit =
    iter_subtree_from_trans
      (fun ~parent id -> ignore (new_node ~parent id)) parent trans_id

  let send_new_subtree_from_file f =
    iter_subtree_from_file (fun ~parent id -> ignore (new_node ~parent id))
      f

  let reset_and_send_the_whole_tree (): unit =
    P.notify Reset_whole_tree;
    iter_on_files
      ~on_file:(fun file -> read_and_send (file_name file))
      ~on_subtree:(fun ~parent id -> ignore (new_node ~parent id))

  let unfocus () =
    focused_node := Unfocused;
    reset_and_send_the_whole_tree ()

  (* -- send the task -- *)
  let task_of_id d id do_intros show_full_context loc =
    let task,tables =
      if do_intros then get_task d.cont.controller_session id
      else
        let task = get_raw_task d.cont.controller_session id in
        let tables = Args_wrapper.build_naming_tables task in
        task,tables
    in
    (* This function also send source locations associated to the task *)
    let loc_color_list = if loc then get_locations task else [] in
    let task_text =
      let pr = tables.Trans.printer in
      let apr = tables.Trans.aprinter in
      let module P = (val Pretty.create pr apr pr pr false) in
      Pp.string_of (if show_full_context then P.print_task else P.print_sequent) task
    in
    task_text, loc_color_list

  let send_task nid do_intros show_full_context loc =
    let d = get_server_data () in
    match any_from_node_ID nid with
    | APn id ->
       let s, list_loc = task_of_id d id do_intros show_full_context loc in
       P.notify (Task (nid, s, list_loc))
    | ATh t ->
       P.notify (Task (nid, "Theory " ^ (theory_name t).Ident.id_string, []))
    | APa pid ->
       let pa = get_proof_attempt_node  d.cont.controller_session pid in
       let parid = pa.parent in
       let name = Pp.string_of Whyconf.print_prover pa.prover in
       let s, list_loc = task_of_id d parid do_intros show_full_context loc in
       P.notify (Task (nid,s ^ "\n====================> Prover: " ^ name ^ "\n", list_loc))
    | AFile f ->
       P.notify (Task (nid, "File " ^ file_name f, []))
    | ATn tid ->
       let name = get_transf_name d.cont.controller_session tid in
       let args = get_transf_args d.cont.controller_session tid in
       let parid = get_trans_parent d.cont.controller_session tid in
       let s, list_loc = task_of_id d parid do_intros show_full_context loc in
       P.notify (Task (nid, s ^ "\n====================> Transformation: " ^ String.concat " " (name :: args) ^ "\n", list_loc))

  (* -------------------- *)

  (* Add a file into the session when (Add_file_req f) is sent *)
  (* Note that f is the path from execution directory to the file and fn is the
     path from the session directory to the file. *)
  let add_file_to_session cont f =
    let fn = Sysutil.relativize_filename
      (get_dir cont.controller_session) f in
    let fn_exists =
      try Some (get_file cont.controller_session fn)
      with | Not_found -> None
    in
    match fn_exists with
    | None ->
        if (Sys.file_exists f) then
          begin
            match add_file cont f with
            | [] ->
               let file = get_file cont.controller_session fn in
               send_new_subtree_from_file file;
               read_and_send (file_name file);
               P.notify (Message (Information "file added in session"))
            | l ->
               read_and_send fn;
               List.iter
                 (function
                   | (loc,rel_loc,s) ->
                      P.notify (Message (Parse_Or_Type_Error(loc,rel_loc,s))))
                 l
          end
        else
          P.notify (Message (Open_File_Error ("File not found: " ^ f)))
    | Some _ -> P.notify (Message (Open_File_Error ("File already in session: " ^ fn)))


  (* ------------ init server ------------ *)

  let init_server ?(send_source=true) config env f =
    Debug.dprintf debug "loading session %s@." f;
    let ses,use_shapes = Session_itp.load_session f in
    Debug.dprintf debug "creating controller@.";
    let c = create_controller config env ses in
    (* let task_driver = task_driver config env in*)
    server_data := Some
                     { (* task_driver = task_driver; *)
                       cont = c;
                       send_source = send_source;
                     };
    let d = get_server_data () in
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
    let transformation_list = List.map fst (list_transforms ()) in
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
    Debug.dprintf debug "sending initialization infos@.";
    P.notify (Initialized infos);
    Debug.dprintf debug "reloading source files@.";
    let x = reload_files d.cont ~use_shapes in
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
    begin match pa_status with
          | UpgradeProver _ ->
             let n = get_node_name (APa panid) in
             P.notify (Node_change (node_id, Name_change n))
          | _ -> ()
    end;
    let pa = get_proof_attempt_node ses panid in
    let new_status =
      Proof_status_change (pa_status, pa.proof_obsolete, pa.limit)
    in
    P.notify (Node_change (node_id, new_status))

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

  let schedule_proof_attempt ~counterexmp nid (p: Whyconf.config_prover) limit =
    let d = get_server_data () in
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof d.cont in
    let unproven_goals = unproven_goals_below_id d.cont (any_from_node_ID nid) in
    List.iter (fun id -> C.schedule_proof_attempt d.cont id prover ~counterexmp
                ~limit ~callback ~notification:(notify_change_proved d.cont))
      unproven_goals

  let schedule_edition (nid: node_ID) (p: Whyconf.config_prover) =
    let d = get_server_data () in
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof d.cont in
    try
      let id =
        match any_from_node_ID nid with
        | APn id -> id
        | APa panid -> get_proof_attempt_parent d.cont.controller_session panid
        | _ -> raise Not_found
      in
      C.schedule_edition d.cont id prover
                           ~callback ~notification:(notify_change_proved d.cont)
    with Not_found ->
      P.notify
        (Message
           (Information
              "for edition please select either a goal or a proof attempt"))

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
    | TSfailed (id, e) ->
      let doc = try
        Pp.sprintf "%s\n%a" tr Pp.formatted (Trans.lookup_trans_desc tr)
      with | _ -> "" in
      let msg, loc, arg_opt = get_exception_message d.cont.controller_session id e in
      let tr_applied = tr ^ " " ^ (List.fold_left (fun x acc -> x ^ " " ^ acc) "" args) in
      P.notify (Message (Transf_error (node_ID_from_pn id, tr_applied, arg_opt, loc, msg, doc)))
    | _ -> ()

  let rec apply_transform nid t args =
    let d = get_server_data () in
    match any_from_node_ID nid with
    | APn id ->
      let callback = callback_update_tree_transform t args in
      C.schedule_transformation d.cont id t args ~callback ~notification:(notify_change_proved d.cont)
    | APa panid ->
      let parent_id = get_proof_attempt_parent d.cont.controller_session panid in
      let parent = node_ID_from_pn parent_id in
      apply_transform parent t args
    | ATn _ | AFile _ | ATh _ ->
      (* TODO: propagate trans to all subgoals, just the first one, do nothing ... ?  *)
      ()

  let removed x =
    let nid = node_ID_from_any x in
    remove_any_node_ID x;
    P.notify (Remove nid)


  let schedule_bisection (nid: node_ID) =
    let d = get_server_data () in
    try
      let id =
        match any_from_node_ID nid with
        | APa panid -> panid
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


  (* ----------------- run strategy -------------------- *)

  let debug_strat = Debug.register_flag "strategy_exec" ~desc:"Trace strategies execution"

  let run_strategy_on_task ~counterexmp nid s =
    let d = get_server_data () in
    let unproven_goals = unproven_goals_below_id d.cont (any_from_node_ID nid) in
    try
      let (n,_,_,st) = Hstr.find d.cont.controller_strategies s in
      Debug.dprintf debug_strat "[strategy_exec] running strategy '%s'@." n;
      let callback sts =
        Debug.dprintf debug_strat "[strategy_exec] strategy status: %a@." print_strategy_status sts
      in
      let callback_pa = callback_update_tree_proof d.cont in
      let callback_tr tr args st = callback_update_tree_transform tr args st in
      List.iter (fun id ->
                 C.run_strategy_on_goal d.cont id st ~counterexmp
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
    let n = any_from_node_ID nid in
    begin
      try
        remove_subtree
          ~notification:(notify_change_proved d.cont)
          ~removed
          d.cont n
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
    Hstr.clear file_to_node_ID

  let reload_session () : unit =
    let d = get_server_data () in
    (* interrupt all running provers and unfocus before reload *)
    C.interrupt ();
    let _old_focus = !focused_node in
    unfocus ();
    clear_tables ();
    let l = reload_files d.cont ~use_shapes:true in
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
    let final_callback lr =
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

  (* ----------------- locate next unproven node -------------------- *)

  let notify_first_unproven_node d ni =
    let s = d.cont.controller_session in
    let any = any_from_node_ID ni in
      let unproven_any =
        get_first_unproven_goal_around
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


  (* ----------------- treat_request -------------------- *)


  let treat_request r =
    let d = get_server_data () in
    let config = d.cont.controller_config in
    try (
    match r with
    | Save_req                     -> save_session ()
    | Reload_req                   -> reload_session ()
    | Get_first_unproven_node ni   ->
      notify_first_unproven_node d ni
    | Focus_req nid ->
        let d = get_server_data () in
        let s = d.cont.controller_session in
        let any = any_from_node_ID nid in
        let focus_on =
          match any with
          | APa pa -> APn (Session_itp.get_proof_attempt_parent s pa)
          | _ -> any
        in
        focused_node := Focus_on [focus_on];
        reset_and_send_the_whole_tree ()
    | Unfocus_req -> unfocus ()
    | Remove_subtree nid           -> remove_node nid
    | Copy_paste (from_id, to_id)    ->
        let from_any = any_from_node_ID from_id in
        let to_any = any_from_node_ID to_id in
        C.copy_paste ~notification:(notify_change_proved d.cont)
          ~callback_pa:(callback_update_tree_proof d.cont)
          ~callback_tr:(callback_update_tree_transform)
          d.cont from_any to_any
    | Get_file_contents f          ->
        read_and_send f
    | Save_file_req (name, text)   ->
        save_file name text;
    | Get_task(nid,b,c,loc)         -> send_task nid b c loc
    | Interrupt_req                -> C.interrupt ()
    | Command_req (nid, cmd)       ->
      begin
        let snid = try Some(any_from_node_ID nid) with Not_found -> None in
        match interp commands_table d.cont snid cmd with
        | Transform (s, _t, args) -> apply_transform nid s args
        | Query s                 -> P.notify (Message (Query_Info (nid, s)))
        | Prove (p, limit)        ->
            let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
            schedule_proof_attempt ~counterexmp nid p limit
        | Strategies st           ->
            let counterexmp = Whyconf.cntexample (Whyconf.get_main config) in
            run_strategy_on_task ~counterexmp nid st
        | Edit p                  -> schedule_edition nid p
        | Bisect                  -> schedule_bisection nid
        | Replay valid_only       -> replay ~valid_only snid
        | Clean                   -> clean snid
        | Mark_Obsolete           -> mark_obsolete snid
        | Help_message s          -> P.notify (Message (Help s))
        | QError s                -> P.notify (Message (Query_Error (nid, s)))
        | Other (s, _args)        ->
            P.notify (Message (Information ("Unknown command: "^s)))
      end
    | Add_file_req f ->
      add_file_to_session d.cont f;
(*      let f = Sysutil.relativize_filename
          (Session_itp.get_dir d.cont.controller_session) f in
         read_and_send f *)
      ()
(*
    | Open_session_req file_or_dir_name ->
        let b = init_cont file_or_dir_name in
        if b then
          reload_session ()
        else
          () (* Eventually print debug here *)
*)
    | Set_config_param(s,i)   ->
       begin
         match s with
         | "max_tasks" -> Controller_itp.set_session_max_tasks i
         | "timelimit" -> Server_utils.set_session_timelimit i
         | "memlimit" -> Server_utils.set_session_memlimit i
         | _ -> P.notify (Message (Error ("Unknown config parameter "^s)))
       end
    | Exit_req                -> exit 0
     )
    with e when not (Debug.test_flag Debug.stack_trace)->
      P.notify (Message (Error (Pp.string_of
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
    S.timeout ~ms:default_delay_ms treat_requests;
    (* S.idle ~prio:1 treat_requests; *)
    C.register_observer update_monitor

end
