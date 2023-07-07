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

open Format
open Ident
open Term
open Ity
open Expr
open Model_parser
open Pinterp_core
open Pinterp

let debug_check_ce_rac_results = Debug.register_info_flag "check_ce:rac_results"
    ~desc:"Debug@ info@ about@ RAC@ results@ for@ --check-ce"

let debug_check_ce_categorization = Debug.register_info_flag "check_ce:categorization"
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
        (Pp.print_option_or_default "unknown location" Loc.pp_position)
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

(** Import values from SMT solver models to interpreter values. *)

let cannot_import f =
  incomplete ("cannot import value from model: " ^^ f)

let rec import_model_value loc env check known ity t =
  Debug.dprintf debug_check_ce_rac_results "[import_model_value] importing term %a with type %a@."
    Pretty.print_term t
    (Pp.print_option Pretty.print_ty) t.t_ty;
  Debug.dprintf debug_check_ce_rac_results "[import_model_value] expected type = %a@."
    Ity.print_ity ity;
  let res =
    if Opt.equal Ty.ty_equal (Some (ty_of_ity ity)) t.t_ty then
      match t.t_node with
      | Tvar _ -> undefined_value env ity
      | Ttrue -> bool_value true
      | Tfalse -> bool_value false
      | _ when t_equal t t_bool_true -> bool_value true
      | _ when t_equal t t_bool_false -> bool_value false
      | Tapp (ls, args) -> (
          (* create a constructor value if ls corresponds to a constructor,
             otherwise create a term value *)
          let ts, l1, l2 = ity_components ity in
          let subst = its_match_regs ts l1 l2 in
          let def = Pdecl.find_its_defn known ts in
          let matching_name rs = String.equal rs.rs_name.id_string ls.ls_name.id_string in
          match List.find matching_name def.Pdecl.itd_constructors with
          | rs -> (
            let itys = List.map (fun pv -> ity_full_inst subst pv.pv_ity)
                rs.rs_cty.cty_args in
            let args =
              List.map2 (import_model_value loc env check known) itys args
            in
            constr_value ity (Some rs) def.Pdecl.itd_fields args)
          | exception Not_found -> term_value ity t)
      | Teps tb ->
        begin
          let exception UnexpectedPattern in
          match Term.t_open_lambda t with
          | [], _, _ ->
            (* special cases for range types and records represented as epsilon terms *)
            begin
              let x_eps, t' = t_open_bound tb in
              (* special case for range types:
                if t is of the form epsilon x:ty. ty'int x = v, check that v is in the
                range of values defined by type ty *)
              try
                let (proj_ls, proj_v) =
                  match t'.t_node with
                  | Tapp (ls, [proj;term_value]) when ls_equal ls ps_equ -> (
                    match proj.t_node with
                    | Tapp (ls, [x]) when t_equal x (t_var x_eps) -> (ls,term_value)
                    | _ -> raise UnexpectedPattern
                  )
                  | _ -> raise UnexpectedPattern
                in
                let valid_range =
                  match ity_components ity, proj_v with
                  | ({ its_def = Ty.Range r; its_ts= ts }, _, _),
                    { t_node= Tconst (Constant.ConstInt c) }
                    when proj_ls.ls_name.id_string = ts.Ty.ts_name.id_string ^ "'int"
                      && Opt.equal Ty.ty_equal proj_ls.ls_value (Some Ty.ty_int) -> (
                      try Number.(check_range c r); true
                      with Number.OutOfRange _ -> false )
                  | _ -> raise UnexpectedPattern
                in
                if valid_range then
                  term_value ity t
                else
                  let desc = asprintf "for range projection %a" print_ity ity in
                  let cntr_ctx = mk_cntr_ctx env ~desc ~giant_steps:None Vc.expl_pre in
                  stuck ?loc cntr_ctx "%s" desc
              with
              | UnexpectedPattern ->
              (* check if t is of the form epsilon x:ty. x.f1 = v1 /\ ... /\ x.fn = vn
              with f1,...,fn the fields associated to the record type ity *)
              let ts, l1, l2 = ity_components ity in
              let subst = its_match_regs ts l1 l2 in
              let def = Pdecl.find_its_defn known ts in
              let rec get_conjuncts t' = match t'.t_node with
                | Tbinop (Tand, t1, t2) -> t1 :: (get_conjuncts t2)
                | _ -> [t']
              in
              try
                let list_of_fields_values =
                  List.fold_left
                    (fun acc c ->
                      match c.t_node with
                      | Tapp (ls, [proj;term_value]) when ls_equal ls ps_equ -> (
                        match proj.t_node with
                        | Tapp (ls, [x]) when t_equal x (t_var x_eps) ->
                          (ls,term_value) :: acc
                        | _ -> raise UnexpectedPattern
                      )
                      | _ -> raise UnexpectedPattern
                    )
                    []
                    (get_conjuncts t')
                in
                let field_values =
                  List.map
                    (fun field_rs ->
                      let field_ity = ity_full_inst subst (fd_of_rs field_rs).pv_ity in
                      let matching_field_name rs (ls,_) =
                        String.equal ls.ls_name.id_string rs.rs_name.id_string in
                      match List.find_all (matching_field_name field_rs) list_of_fields_values with
                      | [(_ls,term_value)] ->
                        import_model_value loc env check known field_ity term_value
                      | [] ->
                        (* if the epsilon term does not define a value for field_rs,
                          use undefined value *)
                        undefined_value env field_ity
                      | _ -> raise UnexpectedPattern
                      )
                    def.Pdecl.itd_fields
                in
                if (List.length field_values > 0) then
                  constr_value ity None def.Pdecl.itd_fields field_values
                else raise UnexpectedPattern
              with
              | UnexpectedPattern -> term_value ity t
            end
          | _ -> term_value ity t
        end
      | _ -> term_value ity t
    else
      (* [ity] and the type of [t] may not match for the following reason:
         [t] is actually the content of a reference (i.e. a record with a single field) *)
      let ts, l1, l2 = ity_components ity in
      let subst = its_match_regs ts l1 l2 in
      let def = Pdecl.find_its_defn known ts in
      match def.Pdecl.itd_constructors, def.Pdecl.itd_fields with
        | [rs], [field_rs] ->
          let field_ity = ity_full_inst subst (fd_of_rs field_rs).pv_ity in
          constr_value ity (Some rs) [field_rs]
            [import_model_value loc env check known field_ity t]
        | _ ->
          cannot_import "type %a with %d constructor(s) and %d field(s) while expecting a single field record"
            print_its ts
            (List.length def.Pdecl.itd_constructors)
            (List.length def.Pdecl.itd_fields)
  in
  check ity res;
  Debug.dprintf debug_check_ce_rac_results "[import_model_value] res = %a@."
    Pinterp_core.print_value res;
  res

let oracle_of_model pm model =
  let import check oid loc env ity me =
    let loc = if loc <> None then loc else
        match oid with Some id -> id.id_loc | None -> None in
    import_model_value loc env check pm.Pmodule.mod_known ity me.me_value in
  let for_variable env ?(check=fun _ _ -> ()) ~loc id ity =
    Opt.map (import check (Some id) loc env ity)
      (search_model_element_for_id model ?loc id) in
  let for_result env ?(check=fun _ _ -> ()) ~loc ~call_id ity =
    Opt.map (import check None (Some loc) env ity)
      (search_model_element_call_result model call_id) in
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

type rs_or_term = RTrsymbol of rsymbol | RTterm of (Decl.prsymbol * term)

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
    let maybe b r = if b then Some (RTrsymbol r) else None in
    match pd.pd_node with
    | PDtype ds ->
       let in_tdef td =
         List.exists (find_in_term loc) td.itd_invariant ||
         Opt.exists in_e td.itd_witness in
       let find_td td = (* TODO *)
         if in_tdef td then Loc.warning
             "Can't check CE for VC from type definitions :(";
         None in
       find_in_list find_td ds
    | PDlet ld ->
       (match ld with
        | LDvar (_, e) -> (* TODO *)
            if in_e e then Loc.warning
                "Can't check CE for VC from variable definitions :(";
           None
        | LDsym (rs, ce) -> maybe (in_cty rs.rs_cty || in_ce ce) rs
        | LDrec defs ->
           let in_def d = in_cty d.rec_sym.rs_cty || in_ce d.rec_fun in
           find_in_list (fun d -> maybe (in_def d) d.rec_sym) defs)
    | PDexn _
    | PDpure -> None
  and find_decl d =
    let maybe b pr t = if b then Some (RTterm(pr, t)) else None in
    Decl.(match d.d_node with
    | Dtype _ | Ddata _ | Dparam _ | Dlogic _ | Dind _ -> None
    | Dprop (_,pr,t) ->
        if Opt.equal Loc.equal (Some loc) pr.pr_name.id_loc then Some (RTterm (pr,t)) else
          maybe (find_in_term loc t) pr t)
  and find_mod_unit = function
    | Uuse _ | Uclone _ | Umeta _ -> None
    | Uscope (_, us) -> find_in_list find_mod_unit us
    | Udecl pd -> find_pdecl pd
  and find_mod_theory td =
    Theory.(match td.td_node with
    | Use _ | Clone _ | Meta _ -> None
    | Decl d -> find_decl d)
  in
  match find_in_list find_mod_unit pm.mod_units with
  | Some rs -> Some rs
  | None -> find_in_list find_mod_theory pm.mod_theory.Theory.th_decls

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
        Pp.print_option_or_default "unknown location" Loc.pp_position in
      let reason = asprintf "%s at %a" reason print_oloc l in
      Res_stuck reason, Log.flush_log ctx.cntr_env.log_uc
  | Incomplete reason ->
      let reason = sprintf "terminated because %s" reason in
      Res_incomplete reason, Log.empty_log
  | _ ->
      let reason = sprintf "terminated with uncaught exception" in
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
    Debug.dprintf debug_check_ce_rac_results "@[Check model %d (@[%a@])@]@." i
      (Pp.print_option_or_default "NO LOC" Loc.pp_position)
      (get_model_term_loc m);
    let normal_res, giant_res = match get_model_term_loc m with
    | None ->
        rac_not_done_failure "no location annotation found in the term triggering the VC"
    | Some loc ->
        if Loc.equal loc Loc.dummy_position then
          rac_not_done_failure "the term triggering the VC has a dummy location annotation"
        else
          begin
            match find_rs env.pmodule loc with
            | Some (RTrsymbol rs) ->
                let rac_execute ~giant_steps rs model =
                  let ctx = Pinterp.mk_ctx env ~do_rac:true ~giant_steps ~rac
                        ~oracle:(oracle_of_model env.pmodule model) ~compute_term
                        ?timelimit ?steplimit () in
                  rac_execute ctx rs
                in
                let print_attrs = Debug.test_flag Call_provers.debug_attrs in
                Debug.dprintf debug_check_ce_rac_results
                  "@[Checking model:@\n@[<hv2>%a@]@]@\n"
                  (print_model ~filter_similar:false ~print_attrs) m;
                begin
                let giant_state,giant_log = rac_execute ~giant_steps:true rs m in
                match only_giant_step with
                | None | Some false ->
                    let normal_state,normal_log = rac_execute ~giant_steps:false rs m in
                    RAC_done (normal_state,normal_log), RAC_done (giant_state,giant_log)
                | Some true ->
                    RAC_not_done "only_giant_step", RAC_done (giant_state,giant_log)
                end
            | Some (RTterm(pr,t)) ->
                let cty = Expr.cty_from_formula t in
                let name = pr.Decl.pr_name.id_string ^ "'goal" in
                let rs = Expr.create_rsymbol (Ident.id_derive name pr.Decl.pr_name) cty in
                let body =
                  c_fun cty.cty_args cty.cty_pre cty.cty_post cty.cty_xpost cty.cty_oldies e_void
                in
                let env = { env with funenv = Mrs.add rs (body,None) env.funenv } in
                let rac_execute ~giant_steps rs model =
                  let ctx = Pinterp.mk_ctx env ~do_rac:true ~giant_steps ~rac
                        ~oracle:(oracle_of_model env.pmodule model) ~compute_term
                        ?timelimit ?steplimit () in
                  rac_execute ctx rs
                in
                let print_attrs = Debug.test_flag Call_provers.debug_attrs in
                Debug.dprintf debug_check_ce_rac_results
                  "@[Checking model:@\n@[<hv2>%a@]@]@\n"
                  (print_model ~filter_similar:false ~print_attrs) m;
                begin
                let state,log = rac_execute ~giant_steps:false rs m in
                RAC_done (state,log), RAC_done (state,log)
                end
            | None ->
                Format.kasprintf (fun s -> rac_not_done_failure s)
                  "there is no program function to execute at %a"
                  Loc.pp_position loc
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

(** Transform an interpretation log into a prover model.
    TODO fail if the log doesn't fail at the location of the original model *)
let model_of_exec_log ~original_model log = ignore original_model; ignore log; assert false
(** NOT MAINTAINED since the change of data types in Model_parser.model_value
    to use Term.term *)
(*
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
*)
