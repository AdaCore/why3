(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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

let print_call fmt call =
  let print_oloc =
    Pp.print_option_or_default "unknown location" Loc.pp_position in
  match call.Log.log_desc with
  | Log.Exec_call (Some rs,_,_)  ->
    Format.fprintf fmt "  - Function '%a' at %a" print_rs rs print_oloc call.Log.log_loc
  | Log.Exec_call (None,_,_) -> Format.fprintf fmt "  - Anonymous function at %a" print_oloc call.Log.log_loc
  | Log.Iter_loop _ ->
     Format.fprintf fmt "  - Loop at %a" print_oloc call.Log.log_loc
  | _ -> ()

let report_verdict env fmt (c,log) =
  match c with
  | NC ->
     Format.fprintf fmt
       "The@ program@ does@ not@ comply@ to@ the@ verification@ goal"
  | SW ->
    let calls = Pinterp_core.Log.get_exec_calls_and_loops env log in
    Format.fprintf fmt
      "The@ contracts@ of@ the@ following@ functions/loops@ are@ too@ weak :@.@[%a@]@."
       (pp_print_list print_call) calls
  | NC_SW ->
    let calls = Pinterp_core.Log.get_exec_calls_and_loops env log in
    if List.length calls = 0 then
      (* In this case, either the contracts of the stdlib/builtin functions are
         too weak or the program is non conforming. We make the assumption that
         our functions are always correctly specified so we choose the latter. *)
      Format.fprintf fmt
       "The@ program@ does@ not@ comply@ to@ the@ verification@ goal"
    else
      Format.fprintf fmt
      "The@ program@ does@ not@ comply@ to@ the@ verification@ goal,@ or@ the@ \
        contracts@ of@ the@ following@ functions/loops@ are@ too@ weak :@.@[%a@]@."
       (pp_print_list print_call) calls
  | BAD_CE _ ->
     Format.fprintf fmt
       "Sorry,@ we@ don't@ have@ a@ good@ counterexample@ for@ you@ :("
  | INCOMPLETE reason ->
     Format.fprintf fmt
          "The@ following@ counterexample@ model@ could@ not@ be@ \
           verified@ (%s)" reason

type classification = verdict * Log.exec_log

let print_classification_log_or_model ?verb_lvl ~json ~print_attrs
    fmt (model, (c, log)) =
  let open Json_base in
  if json then
    match c with
    | NC | SW | NC_SW ->
        print_json fmt (Record ["model", json_model model; "log", Log.json_log log])
    | INCOMPLETE _ ->
        print_json fmt (Record ["model", json_model model])
    | BAD_CE _ -> ()
  else
    match c with
    | NC | SW | NC_SW ->
        fprintf fmt "@[%a@]" (Log.print_log ?verb_lvl) log
    | INCOMPLETE _ ->
          fprintf fmt "@[%a@]" (print_model ~print_attrs) model
    | BAD_CE _ -> ()


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
      (Log.print_log ?verb_lvl) log

let is_vc_term ~vc_term_loc ~vc_term_attrs ctx t =
  match vc_term_loc with
  | None -> false
  | Some vc_term_loc ->
      (* The transformation [split_vc] introduces also premises and variables in
         the goal, so we search for the location of the VC term within the term
         [t] where the contradiction has been detected. *)
      let rec has_vc_term_loc t =
        Option.equal Loc.equal (Some vc_term_loc) t.t_loc || match t.t_node with
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

let print_model_classification ?verb_lvl ~json env fmt (m, c) =
  fprintf fmt "@ @[<hov2>%a%t@]"
    (report_verdict env) c
    (fun fmt ->
       match fst c with
       | NC | SW | NC_SW ->
          fprintf fmt ",@ for@ example@ during@ the@ following@ execution:"
       | INCOMPLETE _ ->
           pp_print_string fmt ":"
       | _ -> ());
  let print_attrs = Debug.test_flag Call_provers.debug_attrs in
  fprintf fmt "@ %a"
    (print_classification_log_or_model ?verb_lvl ~print_attrs ~json) (m, c)

(** Import values from SMT solver models to interpreter values. *)

let cannot_import f =
  cannot_evaluate ("cannot import value from model: " ^^ f)

let rec import_model_value loc env check known ity t =
  Debug.dprintf debug_check_ce_rac_results "[import_model_value] importing term %a with type %a@."
    Pretty.print_term t
    (Pp.print_option Pretty.print_ty) t.t_ty;
  Debug.dprintf debug_check_ce_rac_results "[import_model_value] expected type = %a@."
    Ity.print_ity ity;
  let res =
    if Option.equal Ty.ty_equal (Some (ty_of_ity ity)) t.t_ty then
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
                      && Option.equal Ty.ty_equal proj_ls.ls_value (Some Ty.ty_int) -> (
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
    Option.map (import check (Some id) loc env ity)
      (search_model_element_for_id model ?loc id) in
  let for_result env ?(check=fun _ _ -> ()) ~loc ~call_id ity =
    Option.map (import check None (Some loc) env ity)
      (search_model_element_call_result model call_id) in
  { for_variable; for_result }

(** Check and select solver counterexample models *)

let rec find_in_list f = function
  | [] -> None
  | x :: xs -> match f x with
    | None -> find_in_list f xs
    | res -> res

let rec find_in_term loc t =
  Option.equal Loc.equal (Some loc) t.t_loc || t_any (find_in_term loc) t

(* let find_lemma_goal th loc =
 *   let open Theory in
 *   let open Decl in
 *   let in_decl d =
 *     match d.d_node with
 *     | Dprop ((Plemma | Pgoal), pr, t) ->
 *         if Option.equal Loc.equal (Some loc) t.t_loc then
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

let warn_cannot_check_ce =
  Loc.register_warning "cannot_check_ce" "Warn about uncheckable counterexamples"

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
    Option.equal Loc.equal (Some loc) e.e_loc ||
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
         Option.fold ~some:in_e ~none:false td.itd_witness in
       let find_td td = (* TODO *)
         if in_tdef td then Loc.warning warn_cannot_check_ce
             "Can't check CE for VC from type definitions :(";
         None in
       find_in_list find_td ds
    | PDlet ld ->
       (match ld with
        | LDvar (_, e) -> (* TODO *)
            if in_e e then Loc.warning warn_cannot_check_ce
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
        if Option.equal Loc.equal (Some loc) pr.pr_name.id_loc then Some (RTterm (pr,t)) else
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
  | Cannot_decide (ctx,_terms,reason) ->
      let reason = sprintf "terminated because %s" reason in
      Res_incomplete reason, Log.flush_log ctx.cntr_env.log_uc
  | FatalRACError (log, x) when not (Debug.test_flag Debug.stack_trace) ->
      let reason = sprintf "fatal rac error: %s" x in
      Res_incomplete reason, Log.flush_log log
  | x when not (Debug.test_flag Debug.stack_trace) ->
      let reason = sprintf "terminated with uncaught exception `%s`" (Printexc.to_string x) in
      Res_incomplete reason, Log.empty_log

let print_verdict_summary fmt (normal_state, giant_state, v) =
  let pp = print_rac_result_state in
  fprintf fmt "%s@\n@[<v2>- Concrete RAC: %a@]@\n@[<v2>- Abstract RAC: %a@]"
    (string_of_verdict v) pp normal_state pp giant_state

let print_normal_and_giant_rac_results ?verb_lvl fmt (normal_res, giant_res) =
  let pp = print_rac_result ?verb_lvl in
  fprintf fmt "@\n@[<v2>- Concrete RAC: %a@]@\n@[<v2>- Abstract RAC: %a@]"
    pp normal_res pp giant_res

let print_dbg_classified_model selected_ix fmt (i,_,normal_res,giant_res,(v,_)) =
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

(* Functions to convert the values in the RAC execution log to concrete_term *)

let debug_concrete_term = Debug.register_info_flag "debug-concrete-term"
    ~desc:"Print debug messages about the conversion to concrete term"

let id_name {id_string= name; id_attrs= attrs} =
  Ident.(get_model_trace_string ~name ~attrs)
  (* Ident.get_model_trace_string ~name ~attrs *)

let concrete_string_from_vs vs =
  Format.asprintf "@[<h>%a@]" Pretty.print_vs_qualified vs

let concrete_of_ls ls =
  ls.ls_name.id_string

let concrete_of_constant c ty =
  match c with
  | Constant.ConstInt Number.{ il_kind; il_int } ->
    Const (Integer {int_value=Number.{il_kind; il_int};
                    int_verbatim= BigInt.to_string il_int })
  | Constant.ConstReal rconst when Ty.ty_equal ty Ty.ty_real ->
    Const (Real {real_value = rconst;
                 real_verbatim = (asprintf
                      "%a" (Number.(print_real_constant full_support)) rconst)})
  | Constant.ConstReal ({rl_kind; rl_real} as r) -> (* Then it is a float *)
      let ts = match ty.ty_node with | Ty.Tyapp (ts, _) -> ts | _ -> assert false in
      let fp  = begin match ts.ts_def with
      | Float fp -> fp
      | _ -> assert false
      end
      in
      let sign,mant,exp = Number.compute_float r fp in
      let float_sign = {bv_value = BigInt.of_int (if sign then 1 else 0);
                  bv_length = 1;
                  bv_verbatim = if sign then "1" else "0"} in
      let float_exp = {bv_value = exp;
                 bv_length = fp.fp_exponent_digits;
                 bv_verbatim = BigInt.to_string exp} in
      let float_mant = {bv_value = mant;
                  bv_length = fp.fp_significand_digits;
                  bv_verbatim = BigInt.to_string mant} in
      let t_concrete_float_const v =
        Const (
          Float {
            float_exp_size = fp.fp_exponent_digits;
            float_significand_size = fp.fp_significand_digits;
            float_val = v
          })
      in
      t_concrete_float_const
                  (Float_number {
                    float_sign;
                    float_exp;
                    float_mant;
                    float_hex= "" (* TODO *)
                  })
  | Constant.ConstStr s -> Const (String s)

(* Also converts some concrete epsilon terms (was previously done in model_parser):
   - when it represents a record,
   - when it represents the projection of a value
   - when it represents a function that can be unfolded
   to a function literal (used notably for arrays) *)
let rec concrete_term_of_term (pm:Pmodule.pmodule) (m : concrete_syntax_term Mvs.t) =
  function tm ->
    match tm.t_node with
    | Term.Tconst c -> concrete_of_constant c (Option.get tm.t_ty)
    | Term.Tvar v -> (try Mvs.find v m with Not_found -> concrete_var_from_vs v)
    | Term.Tapp (lsymb, ts) ->
      if ls_equal lsymb Term.fs_bool_true then Const (Boolean true)
      else if ls_equal lsymb Term.fs_bool_false then Const (Boolean false)
      else
      begin match get_record pm m lsymb ts with
      | Some t -> t
      | None ->
        let ts_concrete = List.map (concrete_term_of_term pm m) ts in
        let ls_name = concrete_of_ls lsymb in
        Apply (ls_name, ts_concrete)
      end
    | Term.Tif (tif, t1, t2) -> If (concrete_term_of_term pm m tif, concrete_term_of_term pm m t1, concrete_term_of_term pm m t2)
    | Term.Tlet (t, bo) ->
      let v, bo = t_open_bound bo in
      let vstring = concrete_string_from_vs v in
      let updated_m = Mvs.add v (Var vstring) m in
      Let ([(vstring, concrete_term_of_term pm updated_m bo)], concrete_term_of_term pm updated_m t)
    | Term.Teps t ->
      begin match Term.t_open_lambda tm with
      | [], _, _ ->
        (* | Epsilon (eps_x, eps_term) -> *)
        let vs, t' = Term.t_open_bound t in
        begin match get_opt_record pm m vs t' with
        | Some fields_values -> Record fields_values
        | None ->
          begin match get_opt_coercion pm m vs t' with
          | Some (proj_name, v_proj) -> Proj (proj_name,v_proj)
          | None ->
            let vstring = concrete_string_from_vs vs in
            let t'_concrete = concrete_term_of_term pm (Mvs.add vs (Var vstring) m) t' in
            (* TODO an epsilon at this stage is probably an error *)
            Epsilon (vstring, t'_concrete)
          end
        end
      | [vs], trig, t' ->
        begin match get_opt_coercion pm m vs t' with
        | Some (proj_name, v_proj) -> Proj (proj_name,v_proj)
        | None ->
          begin match get_opt_fun_literal pm m vs t' with
          | Some (elts,others) -> FunctionLiteral {elts; others}
          | None ->
            let vstring = concrete_string_from_vs vs in
            let t'_concrete = concrete_term_of_term pm (Mvs.add vs (Var vstring) m) t' in
            Function {args=[vstring]; body=t'_concrete}
          end
        end
      | vsl, trig, t' ->
        let concrete_vars = List.map concrete_string_from_vs vsl in
        let updated_map =
          List.fold_left2 (fun acc v cv ->
            Mvs.add v (Var cv) acc) m vsl concrete_vars
        in
        let t'_concrete = concrete_term_of_term pm updated_map t' in
        Function {args=concrete_vars; body=t'_concrete}
      end
    | Term.Tquant (quant, tq) -> let vs,_, t = t_open_quant tq in
      let quantifier = match quant with
        | Term.Tforall -> Forall
        | Term.Texists -> Exists
      in Quant (quantifier, List.map (fun v -> concrete_string_from_vs v) vs, concrete_term_of_term pm m t)
    | Term.Tbinop (op, t1, t2) ->
      let op = match op with Tand -> And | Tor -> Or | Timplies -> Implies | Tiff -> Iff in
      Binop (op, concrete_term_of_term pm m t1, concrete_term_of_term pm m t2)
    | Term.Tnot t -> Not (concrete_term_of_term pm m t)
    | Term.Ttrue -> Const (Boolean true)
    | Term.Tfalse -> Const (Boolean false)
    | Term.Tcase (_, _) -> failwith "Cannot convert pattern-matching term to model value"

and get_record pm m lsymb args =
  (* Gets the list of record field and value from a term of the form `record'mk t1 ... tn`
     The names for the record fields are obtained from the pmodule *)
  let exception NotRecord in
  begin try
    let ls_ty =
      begin match (Option.get lsymb.ls_value).ty_node with
      | Ty.Tyapp (ts, _) -> ts
      | _ -> raise NotRecord
      end
    in
    let rec find_record_fields (l:Pdecl.its_defn list) =
      begin match l with
      | (d :: rest) -> if Ty.ts_equal d.itd_its.its_ts ls_ty then d.itd_fields
                       else find_record_fields rest
      | [] -> raise NotRecord
      end
    in
    let pdecl = Mid.find lsymb.ls_name pm.mod_known in
    let lsymb_of_rs rs =
      begin match rs.rs_logic with
      | RLls ls -> ls
      | _ -> raise NotRecord
      end
    in
    let fields =
      begin match pdecl.Pdecl.pd_node with
      | PDtype l -> List.map lsymb_of_rs (find_record_fields l)
      | _ -> raise NotRecord
      end
    in
    if
      List.for_all2
        (fun ls t -> Option.equal (Ty.ty_equal) ls.ls_value t.t_ty)
        fields args
    then
      let fields_args = List.map (concrete_term_of_term pm m) args in
      let fields_values =
        List.combine
          (List.map (fun ls ->
            (* FIXME It would be better to always use the qualified name but
               currently it impacts the AdaCore testsuite too much since the model
               trace attribute is expected to be used as a name, and even when
               no model trace is present, the qualified name forbids the recognition
               of the special field names __split_fields and __split_discrs. *)
            (* let ls_name = Format.asprintf "@[<h>%a@]" Pretty.print_ls_qualified ls in *)
            Ident.(get_model_trace_string ~name:ls.ls_name.id_string ~attrs:ls.ls_name.id_attrs))
            fields)
            fields_args
      in
      Some (Record fields_values)
    else
      raise NotRecord
    with NotRecord -> None
  end
and get_opt_record pm env vs t' = None
 (*  (* check if t is of the form epsilon x:ty. x.f1 = v1 /\ ... /\ x.fn = vn
  with f1,...,fn the fields associated to type ty *)
  let exception UnexpectedPattern in
  let rec get_conjuncts t' =
    match t'.t_node with
    | Tbinop (Tand, t1, t2) -> t1 :: (get_conjuncts t2)
    | _ -> [t']
  in
  try
    let expected_fields =
      try Ty.Mty.find (vs.vs_ty) env.type_fields
      with _ -> raise UnexpectedPattern
    in
    let list_of_fields_values =
      List.fold_left
        (fun acc t ->
          match t.t_node with
          | Tapp (ls, [proj;term_value]) when ls_equal ls ps_equ -> (
            match proj.t_node with
            | Tapp (ls, [x]) when t_equal x (t_var vs) ->
              if List.mem ls expected_fields then
                let cterm_value = concrete_term_of_term pm env term_value in
                let ls_name = concrete_of_ls ls in
                (ls_name,cterm_value) :: acc
              else raise UnexpectedPattern
            | _ -> raise UnexpectedPattern
          )
          | _ -> raise UnexpectedPattern
        )
        []
        (get_conjuncts t')
    in
    if List.length expected_fields = List.length list_of_fields_values then
      Some (list_of_fields_values)
    else
      raise UnexpectedPattern
  with UnexpectedPattern -> None *)

and get_opt_coercion pm env vs t =
  (* special case for type coercions:
   if t is of the form epsilon x:ty. proj x = v, use Proj v as concrete term *)
  Debug.dprintf debug_concrete_term "[get_opt_coercion] vs.vs_ty = %a@."
    Pretty.print_ty_qualified vs.vs_ty;
  let is_proj_for_ty ty ls = true
    (*
    We don't have access to a table of projections at this stage?
    match Ty.Mty.find_opt ty env.type_coercions with
    | None -> false
    | Some sls -> List.mem ls (Sls.elements sls) *)
  in
  match t.t_node with
  | Tapp (ls, [proj;term_value]) when ls_equal ls ps_equ -> (
    match proj.t_node with
    | Tapp (proj_ls, [x]) when t_equal x (t_var vs)
             && is_proj_for_ty vs.vs_ty proj_ls ->
      let concrete_proj_v = concrete_term_of_term pm env term_value in
      let ls_name = concrete_of_ls proj_ls in
      Some (ls_name, concrete_proj_v)
    | _ -> None)
  | _ -> None

and get_opt_fun_literal pm env vs t' =
  (* Unfold a concrete term of the form:
  if x = ct0 then ct1 else if x = ct0' then ct1' else ... else ct2
  to the following result:
  elts = [(ct0,ct1),(ct0',ct1')...]
  others = ct2 *)
  (* Format.printf "get_opt_fun_literal (bvar = %a) %a@." Pretty.print_vs vs Pretty.print_term t'; *)
  let res =
  let rec unfold env vs t' =
    match t'.t_node with
    | Tif ({t_node = Tapp (ls, [x;y])}, t1, t2)
        when ls_equal ls ps_equ &&
        (t_equal (t_var vs) x || t_equal (t_var vs) y) ->
      let (elts, others) = unfold env vs t2 in
      let index = (if t_equal (t_var vs) x then concrete_term_of_term pm env y else concrete_term_of_term pm env x) in
      let value = concrete_term_of_term pm env t1 in
      ({ elts_index = index; elts_value = value } :: elts, others)
    | _ ->
      let t'_concrete = concrete_term_of_term pm env t' in
      ([], t'_concrete)
  in
  if t_v_occurs vs t' = 0 then
    let t'_concrete = concrete_term_of_term pm env t' in
    Some ([],t'_concrete)
  else
    match unfold env vs t' with
    | [], _ -> None
    | elts, others -> Some (elts,others)
  in
    res
  (* in match res with
  | Some x -> Format.printf "get_opt_fun_literal: Some@."; Some x
  | None -> Format.printf "get_opt_fun_literal: None@."; None *)

let rec concrete_of_cexp (pm:Pmodule.pmodule)
  (mpv : concrete_syntax_term Mpv.t) (mv : concrete_syntax_term Mvs.t)
  (c:cexp) : concrete_syntax_term =
  match c.c_node with
| Capp (rs, pvsymbols) ->
  let get_pv pv = Mpv.find_def (Var (concrete_string_from_vs pv.pv_vs)) pv mpv in
  Apply (id_name rs.rs_name, List.map get_pv pvsymbols)
| Cpur (_, _) -> failwith "Cannot convert Cpur to model value"
| Cfun e -> concrete_of_expr pm mpv mv e
| Cany -> failwith "Cannot convert Cany to model value"

and concrete_of_expr (pm:Pmodule.pmodule) (mpv : concrete_syntax_term Mpv.t) (mv : concrete_syntax_term Mvs.t) (e: expr) =
  match e.e_node with
| Econst c -> concrete_of_constant c (Ity.ty_of_ity e.e_ity)
| Evar v -> (Mpv.find_def (Var (concrete_string_from_vs v.pv_vs)) v mpv)
| Eexec (cexp, _) -> concrete_of_cexp pm mpv mv cexp
| Eassign _ -> failwith "Cannot convert assign expr to model value"
| Elet (_, _) -> failwith "Cannot convert let expr to model value"
| Eif (e, e1, e2) -> If (concrete_of_expr pm mpv mv e, concrete_of_expr pm mpv mv e1, concrete_of_expr pm mpv mv e2)
| Ematch (_, _, _) -> failwith "Cannot convert match expr to model value"
| Ewhile (_, _, _, _) -> failwith "Cannot convert while expr to model value"
| Efor (_, _, _, _, _) -> failwith "Cannot convert for expr to model value"
| Eraise (_, _) ->  failwith "Cannot convert raise expr to model value"
| Eexn (_, _) -> failwith "Cannot convert exn expr to model value"
| Eassert (_, _) -> failwith "Cannot convert assert expr to model value"
| Eghost _ -> failwith "Cannot convert ghost expr to model value"
| Epure t -> concrete_term_of_term pm mv t
| Eabsurd -> failwith "Cannot convert absurd expr to model value"

let rec model_value pm v =
  let open Value in
  match v_desc v with
  | Vnum i -> concrete_of_constant (Constant.ConstInt Number.{ il_kind = ILitUnk; il_int = i }) Ty.ty_int
  | Vstring s -> Const (String s)
  | Vbool b -> Const (Boolean b)
  | Vproj (ls, v) -> Proj ((id_name ls.ls_name), model_value pm v)
  | Varray a ->
    let aux i v = {
      elts_index= Const (Integer {
                  int_value= Number.{il_kind = ILitUnk; il_int = BigInt.of_int i};
                  int_verbatim= string_of_int i });
      elts_value= model_value pm v }
    in
    FunctionLiteral {
    elts= List.mapi aux (Array.to_list a);
    (* Others is not handled *)
    others= Epsilon ("_", Const (Boolean true));
    }
  | Vconstr (Some rs, frs, fs) -> (
    let vs = List.map (fun f -> model_value pm (field_get f)) fs in
    if Strings.has_suffix "'mk" rs.rs_name.id_string then
      (* same test for record-ness as in smtv2.ml *)
      let ns = List.map (fun rs -> id_name rs.rs_name) frs in
      Record (List.combine ns vs)
    else
      Apply (id_name rs.rs_name, vs) )
  | Vconstr (None, frs,fs) -> (* TODO if I understand correctly, this is a record as well *)
    let vs = List.map (fun f -> model_value pm (field_get f)) fs in
    let ns = List.map (fun rs -> id_name rs.rs_name) frs in
    Record (List.combine ns vs)
  (* Why does the Vfun case happen? Also, I didn't see these values show up in the end *)
  | Vfun (_vars, bvar, e) -> concrete_of_expr pm Mpv.empty (Mvs.of_list [bvar, Var (concrete_string_from_vs bvar)]) e
  | Vpurefun _  -> failwith "Cannot convert pure fun to model value"
  | Vundefined -> (Const (String "undefined"))
  | Vterm t -> concrete_term_of_term pm Mvs.empty t
  | Vreal r ->
    let dummy_real = Number.real_literal ~radix:10 ~neg:false ~int:"42" ~frac:"" ~exp:None in
    Const (Real {real_value = dummy_real ; real_verbatim = (asprintf "%a" Big_real.print_real r)})
  | Vfloat _ | Vfloat_mode _ -> failwith "Cannot convert float to model value"

(* let model_value pm v =
  Format.printf ">>>> value: %a@." print_value v;
  let the_concrete_term = model_value pm v in
  Format.printf "<<<< concrete_term: %a@." print_concrete_term the_concrete_term;
  the_concrete_term *)

(** In case there is no model element in the smt2 model at a LOC that is present in the RAC log,
    this function fills the missing information to create a model element *)
let model_element_of_unmatched_log_entry ?loc id me_concrete_value ty =
  ignore loc;
  if id.id_string <> "zero" && id.id_string <> "one" then
    let dummy_term = Term.t_true in
    let dummy_ls = create_lsymbol (Ident.id_clone id) [] (Some ty) in
    Some {me_concrete_value;
          me_lsymbol = dummy_ls;
          me_kind = Other;
          me_value = dummy_term;
          me_location = None;
          me_attrs = Sattr.empty}
  else None

let debug_print_original_model = Debug.register_info_flag "print-original-model"
    ~desc:"Print original counterexample model when --check-ce"

let debug_print_derived_model = Debug.register_info_flag "print-derived-model"
    ~desc:"Print derived counterexample model when --check-ce"

(** Transform an interpretation log into a prover model.
    The Pmodule is only used to extract the names of record fields in the
    get_record functions in the case we are converting a Term.term from
    the log. The Records that appear in Pinterp_core.value already contain the
    field names.
    TODO fail if the log doesn't fail at the location of the original model
    *)
let model_of_exec_log pm ~original_model log =
  let me_of_log_entry loc id value =
    (* If the log entry corresponds to an element that is present in the model
    log, we reuse that element and substitute the concrete value. This is not
    great, we should at least check that the symbols correspond.
    If there is no model element in the prover model, we fabricate a minimal model
    element with the information we can extract from the log entry (in particular,
    we have no term and no lsymbol!)*)
    match search_model_element_for_id original_model ~loc id with
  | Some me -> Some {me with me_concrete_value = model_value pm value}
  | None ->
      model_element_of_unmatched_log_entry ~loc id
        (model_value pm value) value.Pinterp_core.Value.v_ty
  in
  let me_of_log_entry e = match e.Log.log_loc with
    | Some loc when not Loc.(equal loc dummy_position) -> (
        match e.Log.log_desc with
        | Log.Val_assumed (id, v) ->
            Option.to_list (me_of_log_entry loc id v)
        | Log.Exec_failed (_, mid) ->
            Mid.fold (fun id v l ->
              Option.to_list (me_of_log_entry loc id v) @ l) mid []
        | Log.Res_assumed (ors,v) ->
          (* Results are expected to have the special name "result"?
             TODO: make this match the model element kind *)
            Option.to_list (Option.bind ors (fun rs ->
              (me_of_log_entry loc (Ident.id_register
              (Ident.id_derive "result" rs.rs_name)) v)))
        | _ -> [])
    | _ -> [] in
  let me_of_log_line e =
    let res = List.concat (List.map me_of_log_entry e) in
    if res = [] then None else Some res in
  let me_of_log_lines mint =
    let res = Wstdlib.Mint.map_filter me_of_log_line mint in
    if Wstdlib.Mint.is_empty res then None else Some res in
  let model_files = (Wstdlib.Mstr.map_filter me_of_log_lines (Log.sort_log_by_loc log)) in
  let derived_model = set_model_files original_model model_files
  in
  let print_attrs = Debug.test_flag Call_provers.debug_attrs in
  Debug.dprintf debug_print_original_model "@[<v>Original model:@\n%a@]@\n@." (print_model ~print_attrs) original_model;
  Debug.dprintf debug_print_derived_model "@[<v>Derived model:@\n%a@]@\n@." (print_model ~print_attrs) derived_model;
  derived_model

let get_rac_results ~limits ?verb_lvl ?compute_term
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
    let p (_prover_answer,m) =
      if is_model_empty m then
        if !found_empty then false
        else (found_empty := true; true)
      else true in
    List.filter p models in
  let rac_not_done_failure reason =
    (RAC_not_done reason, RAC_not_done reason) in
  let add_rac_result i (_prover_answer,m) =
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
                        ~limits () in
                  rac_execute ctx rs
                in
                let print_attrs = Debug.test_flag Call_provers.debug_attrs in
                Debug.dprintf debug_check_ce_rac_results
                  "@[Checking model:@\n@[<hv2>%a@]@]@\n"
                  (print_model ~print_attrs) m;
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
                        ~limits () in
                  rac_execute ctx rs
                in
                let print_attrs = Debug.test_flag Call_provers.debug_attrs in
                Debug.dprintf debug_check_ce_rac_results
                  "@[Checking model:@\n@[<hv2>%a@]@]@\n"
                  (print_model ~print_attrs) m;
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
    m,normal_res,giant_res in
  List.mapi add_rac_result models

let models_from_rac ~limits ?verb_lvl ?compute_term rac env pm models =
  let rac_results =
    get_rac_results ~limits ?compute_term ?verb_lvl rac env pm models
  in
  let add_verdict_and_model_from_log (prover_model,normal_res,giant_res) =
    let model,verdict = match normal_res,giant_res with
    | RAC_not_done reason, _ | _, RAC_not_done reason ->
        prover_model, (INCOMPLETE reason, Log.empty_log)
    | RAC_done (normal_state,normal_log), RAC_done (giant_state,giant_log) ->
        let vc_term_loc = get_model_term_loc prover_model in
        let vc_term_attrs = get_model_term_attrs prover_model in
        let verdict =
        classify ~vc_term_loc ~vc_term_attrs
          ~normal_result:(normal_state,normal_log)
          ~giant_step_result:(giant_state,giant_log)
        in
        let derived_model = model_of_exec_log pm ~original_model:prover_model normal_log
        in derived_model, verdict
    in model,normal_res,giant_res,verdict
  in
  List.map add_verdict_and_model_from_log rac_results

let models_from_giant_step ~limits ?verb_lvl ?compute_term rac env pmodule prover_models =
  let add_model_from_giant_log (original_model,_normal_result,giant_result) =
    match giant_result with
    | RAC_done (_, log) ->
        let derived_model = model_of_exec_log pmodule ~original_model log in
        derived_model,giant_result
    | RAC_not_done _ -> original_model,giant_result
  in
  let results = get_rac_results
      ~limits ?compute_term ?verb_lvl ~only_giant_step:true
      rac env pmodule prover_models
  in
  List.map add_model_from_giant_log results

let best_rac_result = fun indexed_models ->
  let indexed_models = List.mapi (fun i (m,n_res,g_res,v) -> i,m,n_res,g_res,v) indexed_models in
  let first_good_model = fun indexed_models ->
    let open Util in
    let good_models, other_models =
      let is_good (_,_,_,_,(s,_)) = match s with
        | NC | SW | NC_SW -> true
        | BAD_CE _ | INCOMPLETE _ -> false in
      List.partition is_good indexed_models in
    if good_models = [] then
      (* No good models. Prioritize the last, non-empty model as it was done
         before 2020, but penalize bad models. *)
      let classification_index = function
        | INCOMPLETE _ -> 0 | BAD_CE _ -> 1
        | NC | SW | NC_SW -> assert false in
      let compare = cmp [
          cmptr (fun (_,_,_,_,(c,_)) -> classification_index c) (-);
          cmptr (fun (i,_,_,_,_) -> -i) (-);
        ] in
      let not_empty (_,m,_,_,_) = not (Model_parser.is_model_empty m) in
      let non_empty_models = (List.filter not_empty other_models) in
          List.sort compare non_empty_models
    else
      let classification_index = function
        | NC -> 0 | SW -> 1 | NC_SW -> 2
        | INCOMPLETE _ | BAD_CE _ -> assert false in
      let compare = cmp [
          (* prefer NC > SW > NCSW > INCOMPLETE > BAD_CE *)
          cmptr (fun (_,_,_,_,(c,_)) -> classification_index c) (-);
        ] in
      List.sort compare good_models
  in
  let selected, selected_ix =
    match List.nth_opt (first_good_model indexed_models) 0 with
    | None -> None, None
    | Some (i,m,_normal_res,_giant_res,v) -> Some (m,v), Some i
  in
  if indexed_models <> [] then
    Debug.dprintf debug_check_ce_categorization "Categorizations of models:@ %a@."
      Pp.(print_list newline (print_dbg_classified_model selected_ix)) indexed_models;
  selected

let best_giant_step_result = fun models ->
  let open Util in
  let classification_index = function
    | RAC_done (Res_fail _ , _) -> 0
    | RAC_done (Res_normal, _) -> 1
    | RAC_done (Res_stuck _ , _) -> 2
    | RAC_done (Res_incomplete _ , _) -> 3
    | RAC_not_done _ -> 4 in
  let compare = cmp [
      cmptr (fun (_,res) -> classification_index res) (-);
    ] in
  let not_empty (m,_) = not (Model_parser.is_model_empty m) in
  List.nth_opt (List.sort compare (List.filter not_empty models)) 0

let last_nonempty_model = fun models ->
  let not_empty (_,m) = not (Model_parser.is_model_empty m) in
  let models = List.filter not_empty models in
  let models = List.rev models in
  Option.map (fun (_,m) -> m) (List.nth_opt models 0)