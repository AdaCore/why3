(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib
open Ident
open Term
open Ity
open Expr
open Model_parser
open Pinterp_core
open Pinterp

let debug_check_ce_rac_results = Debug.register_info_flag "check-ce-rac-results"
    ~desc:"Debug@ info@ about@ RAC@ results@ for@ --check-ce"

let debug_check_ce_categorization = Debug.register_info_flag "check-ce-categorization"
    ~desc:"Debug@ info@ about@ categorization@ of@ RAC@ results@ for@ --check-ce"

(** Result of checking solvers' counterexample models *)

type verdict = NC | SW | NC_SW | BAD_CE of string | INCOMPLETE of string

let string_of_verdict = function
  | NC -> "NC"
  | SW -> "SW"
  | NC_SW -> "NC_SW"
  | INCOMPLETE _ -> "INCOMPLETE"
  | BAD_CE _ -> "BAD_CE"

let report_verdict ?check_ce fmt = function
  | NC ->
     Format.fprintf fmt
       "The@ program@ does@ not@ comply@ to@ the@ verification@ goal"
  | SW ->
     Format.fprintf fmt
       "The@ contracts@ of@ some@ function@ or@ loop@ are@ too weak"
  | NC_SW ->
     Format.fprintf fmt
       ("The@ program@ does@ not@ comply@ to@ the@ verification@ \
         goal,@ or@ the@ contracts@ of@ some@ loop@ or@ function@ are@ \
         too@ weak")
  | BAD_CE _ ->
     Format.fprintf fmt
       "Sorry,@ we@ don't@ have@ a@ good@ counterexample@ for@ you@ :("
  | INCOMPLETE reason ->
     match check_ce with
     | Some true ->
        fprintf fmt
          "The@ following@ counterexample@ model@ could@ not@ be@ \
           verified@ (%s)"
          reason
     | Some false ->
        fprintf fmt
          ("The@ following@ counterexample@ model@ has@ not@ been@ \
            verified@ (%s,@ missing@ option@ --check-ce)") reason
     | None ->
        fprintf fmt "The@ following@ counterexample@ model@ has@ not@ \
                     been@ verified@ (%s)" reason

type classification = verdict * Log.exec_log

let print_classification_log_or_model ?verb_lvl ?json ~print_attrs
    fmt (model, (c, log)) =
  let open Json_base in
  match json with
  | None | Some `Values -> (
      match c with
      | NC | SW | NC_SW ->
          fprintf fmt "@[%a@]" (Log.print_log ?verb_lvl ~json:false) log
      | INCOMPLETE _ ->
          let print_model fmt m =
            if json = None then print_model_human fmt m
            else print_model (* json values *) fmt m in
          fprintf fmt "@[%a@]" (print_model ~print_attrs) model
      | BAD_CE _ -> ()
    )
  | Some `All -> (
      match c with
      | NC | SW | NC_SW ->
          print_json fmt (Record ["model", json_model model; "log", Log.json_log log])
      | INCOMPLETE _ ->
          print_json fmt (Record ["model", json_model model])
      | BAD_CE _ -> ()
    )

type rac_result_state =
  | Res_normal
  | Res_fail of cntr_ctx * term
  | Res_stuck of string
  | Res_incomplete of string

let string_of_rac_result_state = function
  | Res_normal -> "NORMAL"
  | Res_fail _ -> "FAILURE"
  | Res_stuck _ -> "STUCK"
  | Res_incomplete _ -> "INCOMPLETE"

type rac_result =
  | RAC_not_done of string
  | RAC_done of rac_result_state * Log.exec_log

let print_rac_result_state fmt = function
  | Res_normal -> pp_print_string fmt "NORMAL"
  | Res_fail (ctx, t) ->
      fprintf fmt "FAILURE (%a at %a)"
        Vc.print_expl ctx.attr
        (Pp.print_option_or_default "unknown location" Pretty.print_loc')
        (match ctx.loc with Some _ as loc -> loc | _ -> t.Term.t_loc)
  | Res_stuck reason -> fprintf fmt "STUCK (%s)" reason
  | Res_incomplete reason -> fprintf fmt "INCOMPLETE (%s)" reason

let print_rac_result ?verb_lvl fmt result =
  match result with
  | RAC_not_done reason -> fprintf fmt "RAC not done (%s)" reason
  | RAC_done (st,log) ->
    fprintf fmt "%a@,%a" print_rac_result_state st
      (Log.print_log ?verb_lvl ~json:false) log

let is_vc_term ~vc_term_loc ~vc_term_attrs ctx t =
  match vc_term_loc with
  | None -> false
  | Some vc_term_loc ->
      (* The transformation [split_vc] introduces also premises and variables in
         the goal, so we search for the location of the VC term within the term
         [t] where the contradiction has been detected. *)
      let rec has_vc_term_loc t =
        Opt.equal Loc.equal (Some vc_term_loc) t.t_loc || match t.t_node with
        | Tbinop (Term.Timplies, _, t) -> has_vc_term_loc t
        | Tquant (_, tq) -> let _,_,t = t_open_quant tq in has_vc_term_loc t
        | Tlet (_, tb) -> let _,t = t_open_bound tb in has_vc_term_loc t
        | _ -> false in
      (* FIXME: this check is too strong, because the user may have added their own
         "expl:..." attribute *)
      (Sattr.mem ctx.attr vc_term_attrs || true ) &&
      match ctx.loc with
      | Some loc -> Loc.equal loc vc_term_loc
      | None -> has_vc_term_loc t

let classify ~vc_term_loc ~vc_term_attrs ~normal_result ~giant_step_result =
  let normal_state, normal_log = normal_result in
  let giant_step_state, giant_step_log = giant_step_result in
  match normal_state with
  | Res_fail (ctx, t) ->
      if is_vc_term ~vc_term_loc ~vc_term_attrs ctx t then
        NC, normal_log
      else
        let reason = "..." in
        BAD_CE reason, normal_log
  | Res_stuck reason ->
      BAD_CE reason, normal_log
  | Res_normal -> begin
      match giant_step_state with
      | Res_fail _ ->
          SW, giant_step_log
      | Res_stuck reason -> BAD_CE reason, giant_step_log
      | Res_normal -> BAD_CE "no failure", giant_step_log
      | Res_incomplete reason ->
          INCOMPLETE (sprintf "abstract RAC %s" reason), giant_step_log
    end
  | Res_incomplete normal_reason -> begin
      match giant_step_state with
      | Res_fail _ ->
          NC_SW, giant_step_log
      | Res_normal ->
          INCOMPLETE normal_reason, normal_log
      | Res_incomplete giant_step_reason ->
          if normal_reason = giant_step_reason then
            INCOMPLETE (sprintf "both RAC %s" normal_reason), normal_log
          else
            INCOMPLETE (sprintf "concrete RAC %s, abstract RAC %s"
                          normal_reason giant_step_reason), normal_log
      | Res_stuck giant_step_reason ->
          BAD_CE giant_step_reason, giant_step_log
    end

let print_model_classification ?verb_lvl ?json ?check_ce fmt (m, c) =
  fprintf fmt "@ @[<hov2>%a%t@]"
    (report_verdict ?check_ce) (fst c)
    (fun fmt ->
       match fst c with
       | NC | SW | NC_SW ->
           fprintf fmt ",@ for@ example@ during@ the@ following@ execution:"
       | INCOMPLETE _ ->
           pp_print_string fmt ":"
       | _ -> ());
  let print_attrs = Debug.test_flag Call_provers.debug_attrs in
  fprintf fmt "@ %a"
    (print_classification_log_or_model ?verb_lvl ~print_attrs ?json) (m, c)

(* Import values from solver counterexample model *)

let cannot_import f =
  incomplete ("cannot import value from model: " ^^ f)

let trace_or_name id =
  match get_model_element_name ~attrs:id.id_attrs with
  | name -> if name = "" then id.id_string else name
  | exception Not_found -> id.id_string

let get_or_stuck loc env ity desc = function
  | Some v -> v
  | None ->
      let desc = asprintf "for %s %a" desc print_ity ity in
      let cntr_ctx = mk_cntr_ctx env ~desc ~giant_steps:None Vc.expl_pre in
      stuck ?loc cntr_ctx "%s" desc

let import_model_const ity = function
  | Integer {int_value= v} | Bitvector {bv_value= v} ->
      if ity_equal ity ity_int then
        int_value v
      else if is_range_ty (ty_of_ity ity) then
        range_value ity v
      else
        cannot_import "type %a instead of int or range type" print_ity ity
  | String s ->
      if ity_equal ity ity_str then
        string_value s
      else
        cannot_import "type %a instead of string" print_ity ity
  | Boolean b ->
      if ity_equal ity ity_bool then
        bool_value b
      else
        cannot_import "type %a instead of bool" print_ity ity
  | Decimal _ | Fraction _ | Float _ as v ->
      cannot_import "not implemented for value %a" print_model_const_human v

(** Import a value from the prover model to an interpreter value.

    @raise Exit when the type [ity] and the shape of the the value [v] do not
    match. This may happen when a module that contains a value with an abstract
    type is cloned with different types as instantiations of the abstract type.

    @raise CannotImportModelValue when the value cannot be imported *)
let rec import_model_value loc env check known th_known ity v =
  let ts, l1, l2 = ity_components ity in
  let subst = its_match_regs ts l1 l2 in
  let def = Pdecl.find_its_defn known ts in
  let res = match v with
      | Const c -> import_model_const ity c
      | Var _ -> undefined_value env ity
      | Record r ->
          let rs = match def.Pdecl.itd_constructors with [rs] -> rs | _ ->
            cannot_import "type with not exactly one constructors %a/%d"
              print_its ts (List.length def.Pdecl.itd_constructors) in
          let aux field_rs =
            let field_name = trace_or_name field_rs.rs_name in
            let field_ity = ity_full_inst subst (fd_of_rs field_rs).pv_ity in
            match List.assoc field_name r with
            | v -> import_model_value loc env check known th_known field_ity v
            | exception Not_found ->
                (* TODO Better create a default value? *)
                undefined_value env field_ity in
          let vs = List.map aux def.Pdecl.itd_fields in
          constr_value ity rs def.Pdecl.itd_fields vs
      | Apply (s, vs) ->
          let matching_name rs = String.equal rs.rs_name.id_string s in
          let rs = List.find matching_name def.Pdecl.itd_constructors in
          let itys = List.map (fun pv -> ity_full_inst subst pv.pv_ity)
              rs.rs_cty.cty_args in
          let vs =
            List.map2 (import_model_value loc env check known th_known) itys vs
          in
          constr_value ity rs [] vs
      | Proj (p, x) ->
          (* {p : ity -> ty_res => x: ty_res} : ITY *)
          let search (id, decl) = match decl.Decl.d_node with
            | Decl.Dparam ls when String.equal (trace_or_name id) p -> Some ls
            | _ -> None in
          let ls =
            let iter f = Mid.iter (fun id x -> f (id, x)) th_known in
            try Util.iter_first iter search with Not_found ->
              cannot_import "Projection %s not found" p in
          let ty_res = match ls.ls_value with Some ty -> ty | None ->
            cannot_import "projection %a is predicate" Pretty.print_ls ls in
          let ty_arg = match ls.ls_args with [ty] -> ty | _ ->
            cannot_import "projection %a is no unary function"
              Pretty.print_ls ls in
          if not (Ty.ty_equal ty_arg (ty_of_ity ity)) then
            cannot_import "Cannot import projection %a, argument type %a is not \
                           value type %a"
              Pretty.print_ls ls Pretty.print_ty ty_arg print_ity ity;
          let x =
            import_model_value loc env check known th_known (ity_of_ty ty_res) x
          in
          get_or_stuck loc env ity "range projection" (proj_value ity ls x)
      | Array a ->
          let open Ty in
          if not (its_equal def.Pdecl.itd_its its_func) then
            cannot_import "Cannot import array as %a" print_its def.Pdecl.itd_its;
          let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
            | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
            | _ -> assert false in
          let key_value ix = ix.arr_index_key, ix.arr_index_value in
          let keys, values = List.split (List.map key_value a.arr_indices) in
          let keys =
            List.map (import_model_value loc env check known th_known key_ity)
              keys in
          let values =
            List.map (import_model_value loc env check known th_known value_ity)
              values in
          let mv = Mv.of_list (List.combine keys values) in
          let v0 = import_model_value loc env check known th_known value_ity
              a.arr_others in
          purefun_value ~result_ity:ity ~arg_ity:key_ity mv v0
      | Unparsed s -> cannot_import "unparsed value %s" s
      | Undefined -> undefined_value env ity in
  check ity res;
  res

let oracle_of_model pm model =
  let import check oid loc env ity me =
    let loc = if loc <> None then loc else
        match oid with Some id -> id.id_loc | None -> None in
    import_model_value loc env check pm.Pmodule.mod_known
      pm.Pmodule.mod_theory.Theory.th_known ity me.me_value in
  let for_variable env ?(check=fun _ _ -> ()) ~loc id ity =
    Opt.map (import check (Some id) loc env ity)
      (search_model_element_for_id model ?loc id) in
  let for_result env ?(check=fun _ _ -> ()) ~loc ~call_id ity =
    Opt.map (import check None (Some loc) env ity)
      (search_model_element_call_result model call_id loc) in
  { for_variable; for_result }

(** Check and select solver counterexample models *)

let rec find_in_list f = function
  | [] -> None
  | x :: xs -> match f x with
    | None -> find_in_list f xs
    | res -> res

let rec find_in_term loc t =
  Opt.equal Loc.equal (Some loc) t.t_loc || t_any (find_in_term loc) t

(* let find_lemma_goal th loc =
 *   let open Theory in
 *   let open Decl in
 *   let in_decl d =
 *     match d.d_node with
 *     | Dprop ((Plemma | Pgoal), pr, t) ->
 *         if Opt.equal Loc.equal (Some loc) t.t_loc then
 *           Some t
 *         else begin
 *           if find_in_term loc t then
 *             failwith "found location inside term";
 *           None
 *         end
 *     | _ -> None in
 *   let in_tdecl td =
 *     match td.td_node with
 *     | Decl d -> in_decl d
 *     | _ -> None in
 *   find_in_list in_tdecl th.Theory.th_decls *)

(** Identifies the rsymbol of the definition that contains the given
   position. *)
let find_rs pm loc =
  let open Pmodule in
  let open Pdecl in
  let in_cty cty =
    List.exists (find_in_term loc) cty.cty_pre ||
    List.exists (find_in_term loc) cty.cty_post ||
    Mxs.exists (fun _ -> List.exists (find_in_term loc)) cty.cty_xpost in
  let rec in_e e =
    Opt.equal Loc.equal (Some loc) e.e_loc ||
    match e.e_node with
    | Evar _ | Econst _ | Eassign _ -> false
    | Eexec (ce, cty) -> in_ce ce || in_cty cty
    | Elet (d, e) ->
       (match d with
        | LDvar (_, e') -> in_e e'
        | LDsym (rs, ce) -> in_cty rs.rs_cty || in_ce ce
        | LDrec defs -> List.exists (fun d -> in_ce d.rec_fun) defs) ||
       in_e e
    | Eif (e1, e2, e3) ->
       in_e e1 || in_e e2 || in_e e3
    | Ematch (e, regs, exns) ->
       in_e e || List.exists in_e (List.map snd regs) ||
       List.exists in_e (List.map snd (Mxs.values exns))
    | Ewhile (e1, invs, vars, e2) ->
       in_e e1 || List.exists (find_in_term loc) invs ||
       List.exists (find_in_term loc) (List.map fst vars) || in_e e2
    | Efor (_, _, _, invs, e) ->
       List.exists (find_in_term loc) invs || in_e e
    | Eraise (_, e)
    | Eexn (_, e) -> in_e e
    | Eassert (_, t) -> find_in_term loc t
    | Eghost e -> in_e e
    | Epure t -> find_in_term loc t
    | Eabsurd -> false
  and in_ce ce = match ce.c_node with
    | Cfun e -> in_e e
    | Capp (rs, _) -> in_cty rs.rs_cty
    | Cpur _ | Cany -> false in
  let rec find_pdecl pd =
    let maybe b r = if b then Some r else None in
    match pd.pd_node with
    | PDtype ds ->
       let in_tdef td =
         List.exists (find_in_term loc) td.itd_invariant ||
         Opt.exists in_e td.itd_witness in
       let find_td td = (* TODO *)
         if in_tdef td then Warning.emit
             "Can't check CE for VC from type definitions :(";
         None in
       find_in_list find_td ds
    | PDlet ld ->
       (match ld with
        | LDvar (_, e) -> (* TODO *)
            if in_e e then Warning.emit
                "Can't check CE for VC from variable definitions :(";
           None
        | LDsym (rs, ce) -> maybe (in_cty rs.rs_cty || in_ce ce) rs
        | LDrec defs ->
           let in_def d = in_cty d.rec_sym.rs_cty || in_ce d.rec_fun in
           find_in_list (fun d -> maybe (in_def d) d.rec_sym) defs)
    | PDexn _
    | PDpure -> None
  and find_mod_unit = function
    | Uuse _ | Uclone _ | Umeta _ -> None
    | Uscope (_, us) -> find_in_list find_mod_unit us
    | Udecl pd -> find_pdecl pd in
  find_in_list find_mod_unit pm.mod_units

let rac_execute ctx rs =
  if not (get_do_rac ctx) then
    failwith "rac_execute with RAC disabled";
  if (get_rac ctx).ignore_incomplete then
    failwith "incomplete checks ignored in RAC execute";
  Debug.dprintf debug_check_ce_rac_results "%s RAC@."
    (if get_giant_steps ctx then "Giant-step" else "Normal");
  ignore (Log.flush_log (get_env ctx).log_uc);
  try
    let _, ctx = Pinterp.exec_rs ctx rs in
    Res_normal, Log.flush_log (get_env ctx).log_uc
  with
  | Fail (ctx, t) ->
      Res_fail (ctx, t), Log.flush_log ctx.cntr_env.log_uc
  | Stuck (ctx,l,reason) ->
      let print_oloc =
        Pp.print_option_or_default "unknown location" Pretty.print_loc' in
      let reason = asprintf "%s at %a" reason print_oloc l in
      Res_stuck reason, Log.flush_log ctx.cntr_env.log_uc
  | Incomplete reason ->
      let reason = sprintf "terminated because %s" reason in
      Res_incomplete reason, Log.empty_log

let print_verdict_summary fmt (normal_state, giant_state, v) =
  let pp = print_rac_result_state in
  fprintf fmt "%s@\n@[<v2>- Concrete RAC: %a@]@\n@[<v2>- Abstract RAC: %a@]"
    (string_of_verdict v) pp normal_state pp giant_state

let print_normal_and_giant_rac_results ?verb_lvl fmt (normal_res, giant_res) =
  let pp = print_rac_result ?verb_lvl in
  fprintf fmt "@\n@[<v2>- Concrete RAC: %a@]@\n@[<v2>- Abstract RAC: %a@]"
    pp normal_res pp giant_res

let select_model_last_non_empty models =
  let models = List.filter (fun (_,m) -> not (is_model_empty m)) models in
  match List.rev models with
  | (_,m) :: _ -> Some m
  | [] -> None

type strategy_from_verdict =
  (int * Call_provers.prover_answer * model * rac_result * rac_result * classification) list ->
  (int * Call_provers.prover_answer * model * rac_result * rac_result * classification) list

type strategy_from_rac =
  (int * Call_provers.prover_answer * model * rac_result * rac_result) list ->
  (int * Call_provers.prover_answer * model * rac_result * rac_result) list

let last_non_empty_model: strategy_from_rac = fun models ->
  let open Util in
  let compare = cmp [
      cmptr (fun (i,_,_,_,_) -> -i) (-);
    ] in
  List.filter (fun (_,_,m,_,_) -> not (is_model_empty m))
    (List.sort compare models)

let best_non_empty_giant_step_rac_result: strategy_from_rac = fun models ->
  let open Util in
  let classification_index = function
    | RAC_done (Res_fail _ , _) -> 0
    | RAC_done (Res_normal, _) -> 1
    | RAC_done (Res_stuck _ , _) -> 2
    | RAC_done (Res_incomplete _ , _) -> 3
    | RAC_not_done _ -> 4 in
  let compare = cmp [
      cmptr (fun (_,_,_,_,res) -> classification_index res) (-);
      (* prefer simpler models *)
      cmptr (fun (i,_,_,_,_) -> -i) (-);
    ] in
  let not_empty (_,_,m,_,_) = not (Model_parser.is_model_empty m) in
  List.sort compare (List.filter not_empty models)

let first_good_model: strategy_from_verdict = fun classified_models ->
  let open Util in
  let good_models, other_models =
    let is_good (_,_,_,_,_,(s,_)) = match s with
      | NC | SW | NC_SW -> true
      | BAD_CE _ | INCOMPLETE _ -> false in
    List.partition is_good classified_models in
  if good_models = [] then
    (* No good models. Prioritize the last, non-empty model as it was done
       before 2020, but penalize bad models. *)
    let classification_index = function
      | INCOMPLETE _ -> 0 | BAD_CE _ -> 1
      | NC | SW | NC_SW -> assert false in
    let compare = cmp [
        cmptr (fun (_,_,_,_,_,(c,_)) -> classification_index c) (-);
        cmptr (fun (i,_,_,_,_,_) -> -i) (-);
      ] in
    let not_empty (_,_,m,_,_,_) = not (Model_parser.is_model_empty m) in
    List.sort compare (List.filter not_empty other_models)
  else
    let classification_index = function
      | NC -> 0 | SW -> 1 | NC_SW -> 2
      | INCOMPLETE _ | BAD_CE _ -> assert false in
    let compare = cmp [
        (* prefer NC > SW > NCSW > INCOMPLETE > BAD_CE *)
        cmptr (fun (_,_,_,_,_,(c,_)) -> classification_index c) (-);
        (* prefer simpler models *)
        cmptr (fun (i,_,_,_,_,_) -> i) (-);
      ] in
    List.sort compare good_models

let print_dbg_classified_model selected_ix fmt (i,_,_,normal_res,giant_res,(v,_)) =
  match normal_res, giant_res with
  | RAC_not_done reason, _ | _, RAC_not_done reason ->
      fprintf fmt "RAC not done: %s" reason
  | RAC_done (normal_state, _), RAC_done (giant_state, _) ->
      let mark_selected fmt =
        Pp.string fmt (if selected_ix = Some i then "Selected" else "Checked") in
      fprintf fmt "- @[<v>%t model %d: %a@]" mark_selected i
        print_verdict_summary (normal_state, giant_state, v)

let print_dbg_rac_result_model ~print_normal ~print_giant
    selected_ix fmt (i,_,_,normal_res,giant_res) =
  match normal_res, giant_res with
  | RAC_not_done reason, _ | _, RAC_not_done reason ->
      fprintf fmt "RAC not done: %s" reason
  | RAC_done (normal_state, _), RAC_done (giant_state, _) ->
      let mark_selected fmt =
        Pp.string fmt (if selected_ix = Some i then "Selected" else "Checked") in
      if print_normal then
        fprintf fmt "- @[<v>%t model %d - Concrete RAC: %a@]" mark_selected i
          print_rac_result_state normal_state;
      if print_giant then
        fprintf fmt "- @[<v>%t model %d - Abstract RAC: %a@]" mark_selected i
          print_rac_result_state giant_state

let select_model_from_giant_step_rac_results ?strategy models =
  let strategy = Opt.get_def last_non_empty_model strategy in
  let selected, selected_ix =
    match List.nth_opt (strategy models) 0 with
    | None -> None, None
    | Some (i,_,m,_,s) -> Some (m, s), Some i in
  if models <> [] then
    Debug.dprintf debug_check_ce_categorization "Results of selection of models:@ %a@."
      Pp.(print_list newline 
            (print_dbg_rac_result_model ~print_normal:false ~print_giant:true selected_ix))
        models;
  selected

let select_model_from_verdict models =
  let classified_models =
    let add_verdict (i,r,m,normal_res,giant_res) =
      let verdict = match normal_res,giant_res with
      | RAC_not_done reason, _ | _, RAC_not_done reason ->
          INCOMPLETE reason, Log.empty_log
      | RAC_done (normal_state,normal_log), RAC_done (giant_state,giant_log) ->
          let vc_term_loc = get_model_term_loc m in
          let vc_term_attrs = get_model_term_attrs m in
          classify ~vc_term_loc ~vc_term_attrs 
            ~normal_result:(normal_state,normal_log)
            ~giant_step_result:(giant_state,giant_log)
      in
      i,r,m,normal_res,giant_res,verdict in
    List.map add_verdict models in
  let selected, selected_ix =
    match List.nth_opt (first_good_model classified_models) 0 with
    | None -> None, None
    | Some (i,_,m,_,_,s) -> Some (m, s), Some i in
  if classified_models <> [] then
    Debug.dprintf debug_check_ce_categorization "Categorizations of models:@ %a@."
      Pp.(print_list newline (print_dbg_classified_model selected_ix)) classified_models;
  selected
  
let get_rac_results ?timelimit ?steplimit ?verb_lvl ?compute_term
    ?only_giant_step rac env pm models =
  if rac.ignore_incomplete then
    failwith "ignore incomplete must not be true for selecting models";
  let compute_term =
    match compute_term with
    | None -> Rac.Why.mk_compute_term_lit env ()
    | Some f -> f in
  let env = mk_empty_env env pm in
  let models = (* Keep at most one empty model *)
    let found_empty = ref false in
    let p (_,m) =
      if is_model_empty m then
        if !found_empty then false
        else (found_empty := true; true)
      else true in
    List.filter p models in
  let models =
    let add_index i (r,m) = i,r,m in
    List.mapi add_index models in
  let rac_not_done_failure reason =
    (RAC_not_done reason, RAC_not_done reason) in
  let add_rac_result (i,r,m) =
    Debug.dprintf debug_check_ce_rac_results "Check model %d (%a)@." i
      (Pp.print_option_or_default "NO LOC" Pretty.print_loc')
      (get_model_term_loc m);
    let normal_res, giant_res = match get_model_term_loc m with
    | None -> rac_not_done_failure "model term has no location"
    | Some loc ->
        if Loc.equal loc Loc.dummy_position then
          rac_not_done_failure "the term of the CE model has a dummy location"
        else
          let rac_execute ~giant_steps rs model =
            let ctx = Pinterp.mk_ctx env ~do_rac:true ~giant_steps ~rac
                  ~oracle:(oracle_of_model env.pmodule model) ~compute_term
                  ?timelimit ?steplimit () in
            rac_execute ctx rs
          in
          begin
            match find_rs env.pmodule loc with
            | Some rs ->
                let me_name_trans men = men.Model_parser.men_name in
                let print_attrs = Debug.test_flag Call_provers.debug_attrs in
                Debug.dprintf debug_check_ce_rac_results
                  "@[Checking model:@\n@[<hv2>%a@]@]@\n"
                  (print_model ~filter_similar:false ~me_name_trans ~print_attrs) m;
                begin
                let giant_state,giant_log = rac_execute ~giant_steps:true rs m in
                match only_giant_step with
                | None | Some false ->
                    let normal_state,normal_log = rac_execute ~giant_steps:false rs m in
                    RAC_done (normal_state,normal_log), RAC_done (giant_state,giant_log)
                | Some true ->
                    RAC_not_done "only_giant_step", RAC_done (giant_state,giant_log)
                end
            | None ->
                Format.kasprintf (fun s -> rac_not_done_failure s)
                  "no corresponding routine symbol found for %a"
                  Pretty.print_loc' loc
          end
    in
    Debug.dprintf debug_check_ce_rac_results "@[<v2>Results of RAC executions for model %d:%a@]@." i
      (print_normal_and_giant_rac_results ?verb_lvl) (normal_res, giant_res);
    i,r,m,normal_res,giant_res in
  List.map add_rac_result models

let select_model ?timelimit ?steplimit ?verb_lvl ?compute_term ~check_ce
    rac env pm models =
  if check_ce then
    let rac_results =
      get_rac_results ?timelimit ?steplimit ?compute_term ?verb_lvl rac env pm models
    in
    select_model_from_verdict rac_results
  else
    match select_model_last_non_empty models with
    | None -> None
    | Some m -> Some (m, (INCOMPLETE "not checking CE model", Pinterp_core.Log.empty_log))

(** Transformations interpretation log and prover models *)

let rec model_value v =
  let open Value in
  let id_name {id_string= name; id_attrs= attrs} =
    Ident.get_model_trace_string ~name ~attrs in
  match v_desc v with
  | Vnum i -> Const (Integer { int_value= i; int_verbatim= BigInt.to_string i })
  | Vstring s -> Const (String s)
  | Vbool b -> Const (Boolean b)
  | Vproj (ls, v) -> Proj (ls.ls_name.id_string, model_value v)
  | Varray a ->
      let aux i v = {
        arr_index_key= Const (Integer {
            int_value= BigInt.of_int i;
            int_verbatim= string_of_int i
          });
        arr_index_value= model_value v
      } in
      Array {
        arr_indices= List.mapi aux (Array.to_list a);
        arr_others= Undefined;
      }
  | Vconstr (rs, frs, fs) -> (
      let vs = List.map (fun f -> model_value (field_get f)) fs in
      if Strings.has_suffix "'mk" rs.rs_name.id_string then
        (* same test for record-ness as in smtv2.ml *)
        let ns = List.map (fun rs -> rs.rs_name.id_string) frs in
        Record (List.combine ns vs)
      else
        Apply (id_name rs.rs_name, vs) )
  | Vreal _ | Vfloat _ | Vfloat_mode _
  | Vfun _ | Vpurefun _ | Vterm _ | Vundefined ->
      failwith "Cannot convert interpreter value to model value"

(** Transform an interpretation log into a prover model.
    TODO fail if the log doesn't fail at the location of the original model *)
let model_of_exec_log ~original_model log =
  let me loc id value =
    let name = asprintf "%a" print_decoded id.id_string in
    let men_name = get_model_trace_string ~name ~attrs:id.id_attrs in
    let men_kind = match search_model_element_for_id original_model id with
      | Some me -> me.me_name.men_kind
      | None -> Other in
    let me_name = { men_name; men_kind; men_attrs= id.id_attrs } in
    let me_value = model_value value in
    {me_name; me_value; me_location= Some loc; me_lsymbol_location= None} in
  let aux e = match e.Log.log_loc with
    | Some loc when not Loc.(equal loc dummy_position) -> (
        match e.Log.log_desc with
        | Log.Val_assumed (id, v) ->
            [me loc id v]
        | Log.Exec_failed (_, mid) ->
            Mid.fold (fun id v l -> me loc id v :: l) mid []
        | _ -> [] )
    | _ -> [] in
  let aux_l e =
    let res = List.concat (List.map aux e) in
    if res = [] then None else Some res in
  let aux_mint mint =
    let res = Mint.map_filter aux_l mint in
    if Mint.is_empty res then None else Some res in
  let model_files = (Mstr.map_filter aux_mint (Log.sort_log_by_loc log)) in
  set_model_files original_model model_files
