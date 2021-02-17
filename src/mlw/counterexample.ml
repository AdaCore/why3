(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ident
open Term
open Ity
open Expr
open Format
open Pinterp
open Model_parser

let debug_check_ce = Debug.register_info_flag "check-ce"
    ~desc:"Debug@ info@ for@ --check-ce"

(** Result of checking solvers' counterexample models *)

type ce_summary =
  | NCCE of Log.exec_log
  | SWCE of Log.exec_log
  | NCCE_SWCE of Log.exec_log
  | BAD_CE
  | UNKNOWN of string

let print_ce_summary_kind fmt s =
  let str = match s with
    | NCCE _ -> "NCCE"
    | SWCE _ -> "SWCE"
    | NCCE_SWCE _ -> "NCCE_SWCE"
    | UNKNOWN _ -> "UNKNOWN"
    | BAD_CE -> "BAD_CE" in
  pp_print_string fmt str

let print_ce_summary_title ?check_ce fmt = function
  | NCCE _ ->
     Format.fprintf fmt
       "The@ program@ does@ not@ comply@ to@ the@ verification@ goal"
  | SWCE _ ->
     Format.fprintf fmt
       "The@ contracts@ of@ some@ function@ or@ loop@ are@ underspecified"
  | NCCE_SWCE _ ->
     Format.fprintf fmt
       ("The@ program@ does@ not@ comply@ to@ the@ verification@ \
         goal,@ or@ the@ contracts@ of@ some@ loop@ or@ function@ are@ \
         too@ weak")
  | BAD_CE ->
     Format.fprintf fmt
       "Sorry,@ we@ don't@ have@ a@ good@ counterexample@ for@ you@ :("
  | UNKNOWN reason ->
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

let print_ce_summary_values ?verb_lvl ?json ~print_attrs model fmt s =
  let open Json_base in
  let print_model_field =
    print_json_field "model"
      (print_model_json ?me_name_trans:None ~vc_line_trans:string_of_int) in
  let print_log_field =
    print_json_field "log" (Log.print_log ?verb_lvl ~json:true) in
  match json with
  | None | Some `Values -> (
      match s with
      | NCCE log | SWCE log | NCCE_SWCE log ->
          fprintf fmt "@[%a@]" (Log.print_log ?verb_lvl ~json:false) log
      | UNKNOWN _ ->
          let print_model fmt m =
            if json = None then print_model_human fmt m
            else print_model (* json values *) fmt m in
          fprintf fmt "@[%a@]" (print_model ~print_attrs) model
      | BAD_CE -> ()
    )
  | Some `All -> (
      match s with
      | NCCE log | SWCE log | NCCE_SWCE log ->
          fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
            print_model_field model print_log_field log
      | UNKNOWN _ ->
          fprintf fmt "@[@[<hv1>{%a@]}@]" print_model_field model
      | BAD_CE -> ()
    )

type verdict = Good_model | Bad_model | Dont_know

type full_verdict = {
    verdict  : verdict;
    reason   : string;
    exec_log : Log.exec_log;
  }

let print_verdict fmt = function
  | Good_model -> fprintf fmt "good model"
  | Bad_model -> fprintf fmt "bad model"
  | Dont_know -> fprintf fmt "don't know"

let print_full_verdict ?verb_lvl fmt v =
  fprintf fmt "%a (%s)@,%a"
    print_verdict v.verdict v.reason (Log.print_log ?verb_lvl ~json:false) v.exec_log

type check_model_result =
  | Cannot_check_model of {reason: string}
  | Check_model_result of {abstract: full_verdict; concrete: full_verdict}

let print_check_model_result ?verb_lvl fmt = function
  | Cannot_check_model r ->
      fprintf fmt "@[Cannot check model (%s)@]" r.reason
  | Check_model_result r ->
      fprintf fmt "@[<v>@[<hv2>- Concrete: %a@]@\n@[<hv2>- Abstract: %a@]@]"
        (print_full_verdict ?verb_lvl) r.concrete
        (print_full_verdict ?verb_lvl) r.abstract

let ce_summary v_concrete v_abstract =
  match v_concrete.verdict, v_abstract.verdict with
  | Good_model, _          -> NCCE v_concrete.exec_log
  | Bad_model , Good_model -> SWCE v_abstract.exec_log
  | Dont_know , Good_model -> NCCE_SWCE v_abstract.exec_log
  | Dont_know , Dont_know
  | Dont_know , Bad_model  -> UNKNOWN v_concrete.reason
  | Bad_model , Dont_know  -> UNKNOWN v_abstract.reason
  | Bad_model , Bad_model  -> BAD_CE

let print_counterexample ?verb_lvl ?check_ce ?json fmt (model,ce_summary) =
  fprintf fmt "@ @[<hov2>%a%t@]"
    (print_ce_summary_title ?check_ce) ce_summary
    (fun fmt ->
       match ce_summary with
       | NCCE _ | SWCE _ | NCCE_SWCE _ ->
           fprintf fmt ",@ for@ example@ during@ the@ following@ execution:"
       | UNKNOWN _ ->
           fprintf fmt ":"
       | _ -> ());
  let print_attrs = Debug.(test_flag (lookup_flag "print_model_attrs"))  in
  fprintf fmt "@ %a"
    (print_ce_summary_values ?verb_lvl ~print_attrs ?json model) ce_summary

(* Import values from solver counterexample model *)

exception CannotImportModelValue of string

let check_not_nonfree its_def =
  if its_def.Pdecl.itd_its.its_nonfree then
    let msg = asprintf "value of non-free type %a" print_its its_def.Pdecl.itd_its in
    raise (CannotImportModelValue msg)

let get_field_name rs =
  match get_model_element_name ~attrs:rs.rs_name.id_attrs with
  | exception Not_found -> rs.rs_name.id_string
  | "" -> rs.rs_name.id_string
  | name -> name

(* let empty_model_trace attrs =
 *   try
 *     let a = Ident.get_model_trace_attr ~attrs in
 *     a.attr_string = "model_trace:"
 *   with Not_found -> false *)

(** Import a value from the prover model to an interpreter value. Raises [Exit] if the
    value cannot be imported. *)
let rec import_model_value known th_known ity v =
  let ts, l1, l2 = ity_components ity in
  let subst = its_match_regs ts l1 l2 in
  let def = Pdecl.find_its_defn known ts in
  (* match def.Pdecl.itd_constructors, def.Pdecl.itd_fields with
   * | [rs_constr], [rs_field]
   *   when empty_model_trace rs_field.rs_name.id_attrs ->
   *     (\* type ty = { f[@model_trace:]: ty'} *\)
   *     eprintf "WRAP %a in %a@." print_ity ity print_ity rs_field.rs_cty.cty_result;
   *     let v = import_model_value known th_known rs_field.rs_cty.cty_result v in
   *     constr_value ity rs_constr [v]
   * | _ -> *)
    match v with
      | Integer s ->
          if ity_equal ity ity_int then
            int_value s.int_value
          else if is_range_ty (ty_of_ity ity) then
            range_value ity s.int_value
          else
            kasprintf failwith "import_model_value: found type %a instead of int or range type"
              print_ity ity
      | String s ->
          ity_equal_check ity ity_str;
          string_value s
      | Boolean b ->
          ity_equal_check ity ity_bool;
          bool_value b
      | Record r ->
          check_not_nonfree def;
          let rs = match def.Pdecl.itd_constructors with
            | [rs] -> rs
            | _ -> failwith "import_model_value: type with not exactly one constructors" in
          let aux field_rs =
            let field_name = get_field_name field_rs in
            let field_ity = ity_full_inst subst (fd_of_rs field_rs).pv_ity in
            match List.assoc field_name r with
            | v -> import_model_value known th_known field_ity v
            | exception Not_found ->
                (* TODO Better create a default value? Requires an [Env.env]. *)
                undefined_value ity in
          let vs = List.map aux def.Pdecl.itd_fields in
          constr_value ity rs def.Pdecl.itd_fields vs
      | Apply (s, vs) ->
          check_not_nonfree def;
          let matching_name rs = String.equal rs.rs_name.id_string s in
          let rs = List.find matching_name def.Pdecl.itd_constructors in
          let itys = List.map (fun pv -> ity_full_inst subst pv.pv_ity)
              rs.rs_cty.cty_args in
          let vs = List.map2 (import_model_value known th_known) itys vs in
          constr_value ity rs [] vs
      | Proj (p, x) ->
          let is_proj id _ = id.id_string = p in
          let ls = try
              let _, d = Mid.choose (Mid.filter is_proj th_known) in
              match d.Decl.d_node with Decl.Dparam ls -> ls | _ -> raise Not_found
            with Not_found -> kasprintf failwith "Projection %s not found" p in
          (* eprintf "FOUND PROJECTION for %s in %a: %a:%a->%a ity=%a,%a@." p print_model_value v Pretty.print_ls ls Pp.(print_list arrow Pretty.print_ty) ls.ls_args (Pp.print_option Pretty.print_ty) ls.ls_value print_ity ity print_ity ity; *)
          let ty_arg = match ls.ls_args with [ty] -> ty
            | _ -> kasprintf failwith "import_model_value: projection %s not unary" p in
          if not (Ty.ty_equal ty_arg (ty_of_ity ity)) then raise Exit;
          let x_ty = Opt.get_exn (Failure "import_model_value: projection is predicate") ls.ls_value in
          let x = import_model_value known th_known (ity_of_ty x_ty) x in
          (* eprintf "MAKE PROJ ity=%a ls=%a x=%a:%a@." Pretty.print_ty ty_arg Pretty.print_ls ls print_value x Pretty.print_ty x_ty; *)
          proj_value ity ls x
      | Array a ->
          let open Ty in
          assert (its_equal def.Pdecl.itd_its its_func);
          let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
            | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
            | _ -> assert false in
          let keys, values =
            List.split (List.map (fun ix -> ix.arr_index_key, ix.arr_index_value)
                          a.arr_indices) in
          let keys = List.map (import_model_value known th_known key_ity) keys in
          let values = List.map (import_model_value known th_known value_ity) values in
          let mv = Mv.of_list (List.combine keys values) in
          let v0 = import_model_value known th_known value_ity a.arr_others in
          purefun_value ~result_ity:ity ~arg_ity:key_ity mv v0
      | Undefined -> undefined_value ity
      | Decimal _ | Fraction _ | Float _ | Bitvector _ | Unparsed _ as v ->
          kasprintf failwith "import_model_value: not implemented for value %a"
            print_model_value v

let get_model_value m known th_known =
  fun ?name ?loc ity : Value.value option ->
  match loc with
  | None -> None
  | Some l ->
     let ome = match name with
       | None -> get_model_element_by_loc m l
       | Some s -> get_model_element m s l in
     match ome with
     | None -> None
     | Some me ->
         try Some (import_model_value known th_known ity me.me_value)
         with Exit -> None

(** Check and select solver counterexample models *)

(** Identifies the rsymbol of the definition that contains the given
   position. *)
let find_rs pm loc =
  let open Pmodule in
  let open Pdecl in
  let rec find_in_list f = function
    | [] -> None
    | x :: xs ->
       match f x with None -> find_in_list f xs | res -> res in
  let rec in_t t =
    Opt.equal Loc.equal (Some loc) t.t_loc || t_any in_t t in
  let in_cty cty =
    List.exists in_t cty.cty_pre ||
    List.exists in_t cty.cty_post ||
    Mxs.exists (fun _ -> List.exists in_t) cty.cty_xpost in
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
       in_e e1 || List.exists in_t invs ||
       List.exists in_t (List.map fst vars) || in_e e2
    | Efor (_, _, _, invs, e) ->
       List.exists in_t invs || in_e e
    | Eraise (_, e)
    | Eexn (_, e) -> in_e e
    | Eassert (_, t) -> in_t t
    | Eghost e -> in_e e
    | Epure t -> in_t t
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
         List.exists in_t td.itd_invariant ||
         List.exists in_e td.itd_witness in
       let find_td td = (* TODO *)
         if in_tdef td then Warning.emit "Can't check CE for VC from \
                                          type definitions :(";
         None in
       find_in_list find_td ds
    | PDlet ld ->
       (match ld with
        | LDvar (_, e) -> (* TODO *)
           if in_e e then Warning.emit "Can't check CE for VC from \
                                        variable definitions :(";
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

let check_model_rs ?loc rac env pm rs =
  let abs_msg = if rac.rac_abstract then "abstract" else "concrete" in
  let abs_Msg = String.capitalize_ascii abs_msg in
  try
    let _, env = eval_rs rac env pm rs in
    let reason = sprintf "%s RAC does not confirm the counter-example, no \
                          contradiction during execution" abs_Msg in
    {verdict= Bad_model; reason; exec_log= Log.close_log env.rac.log_uc}
  with
  | Contr (ctx, t) when t.t_loc <> None && Opt.equal Loc.equal t.t_loc loc ->
      let reason = sprintf "%s RAC confirms the counter-example" abs_Msg in
      {verdict= Good_model; reason; exec_log= Log.close_log ctx.c_env.rac.log_uc}
  | Contr (ctx, t) ->
      let reason = asprintf "%s RAC found a contradiction at different location %a"
          abs_Msg (Pp.print_option_or_default "NO LOC" Pretty.print_loc') t.t_loc in
      {verdict= Good_model; reason; exec_log= Log.close_log ctx.c_env.rac.log_uc}
  | CannotImportModelValue msg ->
      let reason = sprintf "cannot import value from model: %s" msg in
      {verdict= Dont_know; reason; exec_log= Log.empty_log}
  | CannotCompute r ->
      (* TODO E.g., bad default value for parameter and cannot evaluate
         pre-condition *)
      let reason = sprintf "%s RAC terminated because %s"
                     abs_Msg r.reason in
      {verdict= Dont_know; reason; exec_log= Log.empty_log}
  | Failure msg ->
      (* E.g., cannot create default value for non-free type, cannot construct
          term for constructor that is not a function *)
      let reason = sprintf "failure: %s" msg in
      {verdict= Dont_know; reason; exec_log= Log.empty_log}
  | RACStuck (env,l) ->
      let reason =
        asprintf "%s RAC, with the counterexample model cannot continue after %a"
          abs_Msg (Pp.print_option Pretty.print_loc') l in
      {verdict= Bad_model; reason; exec_log= Log.close_log env.rac.log_uc}

let check_model reduce env pm model =
  match get_model_term_loc model with
  | None ->
     let reason = "model term has no location" in
     Cannot_check_model {reason}
  | Some loc ->
     (* TODO deal with VCs from goal definitions? *)
     if Loc.equal loc Loc.dummy_position then
       failwith ("Pinterp.check_model: the term of the CE model has a \
                  dummy location, it cannot be used to find the \
                  toplevel definition");
     match find_rs pm loc with
     | Some rs ->
        let check_model_rs ~abstract =
          let {Pmodule.mod_known; mod_theory= {Theory.th_known}} = pm in
          let get_value = get_model_value model mod_known th_known in
          let rac = rac_config ~do_rac:true ~abstract
                      ~skip_cannot_compute:false ~reduce ~get_value () in
          check_model_rs ?loc:(get_model_term_loc model) rac env pm rs in
        Debug.dprintf debug_check_ce
          "@[Validating model:@\n@[<hv2>%a@]@]@\n"
          (print_model ~filter_similar:false ?me_name_trans:None ~print_attrs:false) model;
        Debug.dprintf debug_check_ce "@[Interpreting concretly@]@\n";
        let concrete = check_model_rs ~abstract:false in
        Debug.dprintf debug_check_ce "@[Interpreting abstractly@]@\n";
        let abstract = check_model_rs ~abstract:true in
        Check_model_result {concrete; abstract}
     | None ->
        let reason =
          Format.asprintf "no corresponding routine symbol found for %a"
            Pretty.print_loc' loc in
        Cannot_check_model {reason}

let select_model_last_non_empty models =
  let models = List.filter (fun (_,m) -> not (is_model_empty m)) models in
  match List.rev models with
  | (_,m) :: _ -> Some m
  | [] -> None

type sort_models =
  (int * Call_provers.prover_answer * model * check_model_result * ce_summary) list ->
  (int * Call_provers.prover_answer * model * check_model_result * ce_summary) list

let prioritize_last_non_empty_model: sort_models = fun models ->
  let open Util in
  let compare = cmp [
      cmptr (fun (i,_,_,_,_) -> -i) (-);
    ] in
  List.filter (fun (_,_,m,_,_) -> not (is_model_empty m))
    (List.sort compare models)

let prioritize_first_good_model: sort_models = fun models ->
  let open Util in
  let good_models, other_models =
    let is_good (_,_,_,_,s) = match s with
      | NCCE _ | SWCE _ | NCCE_SWCE _ -> true
      | BAD_CE | UNKNOWN _ -> false in
    List.partition is_good models in
  if good_models = [] then
    (* No interesting models, prioritize the last, non-empty model
       as it was done before 2020, but penalize bad models. *)
    let ce_summary_index = function
      | UNKNOWN _ -> 0 | BAD_CE -> 1 | NCCE _
      | SWCE _ | NCCE_SWCE _ -> assert false in
    let compare = cmp [
        cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
        cmptr (fun (i,_,_,_,_) -> -i) (-);
      ] in
    List.sort compare other_models
  else
    let ce_summary_index = function
      | NCCE _ -> 0 | SWCE _ -> 1 | NCCE_SWCE _ -> 2
      | UNKNOWN _ | BAD_CE -> assert false in
    let compare = cmp [
        (* prefer NCCE > SWCE > NCCE_SWCE > UNKNOWN > BAD *)
        cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
        (* prefer simpler models *)
        cmptr (fun (i,_,_,_,_) -> i) (-);
      ] in
    List.sort compare good_models

let print_dbg_model selected_ix fmt (i,_,_,mr,s) =
  let mark_selected fmt =
    let s = if selected_ix = Some i then "Selected" else "Checked" in
    pp_print_string fmt s in
  match mr with
  | Cannot_check_model {reason} ->
      fprintf fmt "- Couldn't check model: %s" reason
  | Check_model_result r ->
      fprintf fmt
        "- @[<v2>%t model %d (Concrete: %a, Abstract: %a)@ @[Summary: %a@]@]"
        mark_selected i print_verdict r.concrete.verdict
        print_verdict r.abstract.verdict
        (print_ce_summary_title ?check_ce:None) s

let select_model ?verb_lvl ?(check=false) ?(reduce_config=rac_reduce_config ())
    ?sort_models env pmodule models =
  let sort_models = Opt.get_def
      (if check then prioritize_first_good_model
       else prioritize_last_non_empty_model) sort_models in
  let check_model =
    if check then check_model reduce_config env pmodule
    else fun _ -> Cannot_check_model {reason="not checking CE model"} in
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
  let models =
    let add_check_model_result (i,r,m) =
      Debug.dprintf debug_check_ce "Check model %d (%a)@." i
        (Pp.print_option_or_default "NO LOC" Pretty.print_loc')
        (get_model_term_loc m);
      (* Debug.dprintf debug_check_ce "@[<hv2>Model from prover:@\n@[%a@]@]@."
       *   (print_model ?me_name_trans:None ~print_attrs:false) m; *)
      let mr = check_model m in
      Debug.dprintf debug_check_ce "@[<v2>Result of checking model %d:@\n@[%a@]@]@." i
        (print_check_model_result ?verb_lvl) mr;
      i,r,m,mr in
    List.map add_check_model_result models in
  let models =
    let add_ce_summary (i,r,m,mr) =
      let summary = match mr with
        | Cannot_check_model {reason} -> UNKNOWN reason
        | Check_model_result r -> ce_summary r.concrete r.abstract in
      i,r,m,mr,summary in
    List.map add_ce_summary models in
  let selected, selected_ix =
    match List.nth_opt (sort_models models) 0 with
    | None -> None, None
    | Some (i,_,m,_,s) -> Some (m, s), Some i in
  if models <> [] then
    Debug.dprintf debug_check_ce "Models:@\n%a@."
      Pp.(print_list space (print_dbg_model selected_ix)) models;
  selected

(** Transformations interpretation log and prover models *)

let rec model_value v =
  let open Value in
  let id_name {id_string= name; id_attrs= attrs} =
    Ident.get_model_trace_string ~name ~attrs in
  match v_desc v with
  | Vnum i -> Integer { int_value= i; int_verbatim= BigInt.to_string i }
  | Vstring s -> String s
  | Vbool b -> Boolean b
  | Vproj (ls, v) -> Proj (ls.ls_name.id_string, model_value v)
  | Varray a ->
      let aux i v = {
        arr_index_key= Integer {
            int_value= BigInt.of_int i;
            int_verbatim= string_of_int i
          };
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
    let men_kind = match get_model_element_by_id original_model id with
      | Some me -> me.me_name.men_kind
      | None -> Other in
    let me_name = { men_name; men_kind; men_attrs= id.id_attrs } in
    let me_value = model_value value in
    {me_name; me_value; me_location= Some loc; me_term= None} in
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
