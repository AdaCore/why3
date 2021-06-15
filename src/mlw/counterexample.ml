(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
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

let debug_check_ce_summary = Debug.register_info_flag "check-ce-summary"
    ~desc:"Debug@ summary@ for@ --check-ce"

(** Result of checking solvers' counterexample models *)

type ce_summary =
  | NC of Log.exec_log
  | SW of Log.exec_log
  | NCSW of Log.exec_log
  | BAD of Log.exec_log
  | UNKNOWN of string

let print_ce_summary_kind fmt s =
  let str = match s with
    | NC _ -> "NC"
    | SW _ -> "SW"
    | NCSW _ -> "NCSW"
    | UNKNOWN _ -> "UNKNOWN"
    | BAD _ -> "BAD" in
  pp_print_string fmt str

let print_ce_summary_title ?check_ce fmt = function
  | NC _ ->
     Format.fprintf fmt
       "The@ program@ does@ not@ comply@ to@ the@ verification@ goal"
  | SW _ ->
     Format.fprintf fmt
       "The@ contracts@ of@ some@ function@ or@ loop@ are@ underspecified"
  | NCSW _ ->
     Format.fprintf fmt
       ("The@ program@ does@ not@ comply@ to@ the@ verification@ \
         goal,@ or@ the@ contracts@ of@ some@ loop@ or@ function@ are@ \
         too@ weak")
  | BAD _ ->
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
      | NC log | SW log | NCSW log ->
          fprintf fmt "@[%a@]" (Log.print_log ?verb_lvl ~json:false) log
      | UNKNOWN _ ->
          let print_model fmt m =
            if json = None then print_model_human fmt m
            else print_model (* json values *) fmt m in
          fprintf fmt "@[%a@]" (print_model ~print_attrs) model
      | BAD _ -> ()
    )
  | Some `All -> (
      match s with
      | NC log | SW log | NCSW log ->
          fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
            print_model_field model print_log_field log
      | UNKNOWN _ ->
          fprintf fmt "@[@[<hv1>{%a@]}@]" print_model_field model
      | BAD _ -> ()
    )

type result_state = Rnormal | Rfailure of cntr_ctx * term | Rstuck | Runknown

type result = {
    state    : result_state;
    reason   : string;
    exec_log : Log.exec_log;
  }

let print_result_state fmt = function
  | Rnormal -> fprintf fmt "NORMAL"
  | Rfailure _ -> fprintf fmt "FAILURE"
  | Rstuck -> fprintf fmt "STUCK"
  | Runknown -> fprintf fmt "UNKNOWN"

let print_result fmt r =
  match r.state with
  | Rnormal -> fprintf fmt "NORMAL"
  | Rfailure (ctx, t) ->
      fprintf fmt "FAILURE (%a at %a)"
        Vc.print_expl ctx.Pinterp.c_attr
        (Pp.print_option_or_default "unknown location" Pretty.print_loc')
        (match ctx.Pinterp.c_loc with Some _ as loc -> loc | _ -> t.Term.t_loc)
  | Rstuck -> fprintf fmt "STUCK (%s)" r.reason
  | Runknown -> fprintf fmt "UNKNOWN (%s)" r.reason

let print_full_result ?verb_lvl fmt v =
  fprintf fmt "%a@,%a"
    print_result v (Log.print_log ?verb_lvl ~json:false) v.exec_log

type check_model_result =
  | Cannot_check_model of {reason: string}
  | Check_model_result of {abstract: result; concrete: result}

let print_result_summary print_result fmt (mr, s) =
  match mr with
  | Cannot_check_model {reason} ->
      fprintf fmt "CANNOT CHECK: %s" reason
  | Check_model_result r ->
      fprintf fmt "%a@\n@[<v2>- Concrete RAC: %a@]@\n@[<v2>- Abstract RAC: %a@]"
        print_ce_summary_kind s print_result r.concrete print_result r.abstract

let print_check_model_result ?verb_lvl =
  print_result_summary (print_full_result ?verb_lvl)

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
      Sattr.mem ctx.c_attr vc_term_attrs &&
      match ctx.c_loc with
      | Some loc -> Loc.equal loc vc_term_loc
      | None -> has_vc_term_loc t

let ce_summary ~vc_term_loc ~vc_term_attrs = function
  | Cannot_check_model {reason} ->
      UNKNOWN reason
  | Check_model_result r ->
      match r.concrete.state with
      | Rfailure (ctx, t) ->
          if is_vc_term ~vc_term_loc ~vc_term_attrs ctx t then
            NC r.concrete.exec_log
          else
            BAD r.concrete.exec_log
      | Rstuck ->
          BAD r.concrete.exec_log
      | Rnormal -> (
          match r.abstract.state with
          | Rfailure _ ->
              SW r.abstract.exec_log
          | Rstuck -> BAD r.abstract.exec_log
          | Rnormal -> BAD r.abstract.exec_log
          | Runknown ->
              if r.concrete.reason = r.abstract.reason then
                UNKNOWN (sprintf "concrete RAC %s" r.concrete.reason)
              else
                UNKNOWN (sprintf "concrete RAC %s, abstract RAC %s"
                           r.concrete.reason r.abstract.reason) )
      | Runknown -> (
          match r.abstract.state with
          | Rfailure _ ->
              NCSW r.abstract.exec_log
          | Rnormal | Runknown ->
              if r.concrete.reason = r.abstract.reason then
                UNKNOWN (sprintf "concrete RAC %s" r.concrete.reason)
              else
                UNKNOWN (sprintf "concrete RAC %s, abstract RAC %s"
                           r.concrete.reason r.abstract.reason)
          | Rstuck ->
              BAD r.abstract.exec_log )

let print_counterexample ?verb_lvl ?check_ce ?json fmt (model,ce_summary) =
  fprintf fmt "@ @[<hov2>%a%t@]"
    (print_ce_summary_title ?check_ce) ce_summary
    (fun fmt ->
       match ce_summary with
       | NC _ | SW _ | NCSW _ ->
           fprintf fmt ",@ for@ example@ during@ the@ following@ execution:"
       | UNKNOWN _ ->
           fprintf fmt ":"
       | _ -> ());
  let print_attrs = Debug.test_flag Call_provers.debug_attrs in
  fprintf fmt "@ %a"
    (print_ce_summary_values ?verb_lvl ~print_attrs ?json model) ce_summary

(* Import values from solver counterexample model *)

exception CannotImportModelValue of string

let cannot_import f =
  kasprintf (fun msg -> raise (CannotImportModelValue msg)) f

let trace_or_name id =
  match get_model_element_name ~attrs:id.id_attrs with
  | name -> if name = "" then id.id_string else name
  | exception Not_found -> id.id_string

let import_model_const ity = function
  | Integer s ->
      if ity_equal ity ity_int then
        int_value s.int_value
      else if is_range_ty (ty_of_ity ity) then
        range_value ity s.int_value
      else
        cannot_import "type %a instead of int or range type" print_ity ity
  | String s ->
      ity_equal_check ity ity_str;
      string_value s
  | Boolean b ->
      ity_equal_check ity ity_bool;
      bool_value b
  | Decimal _ | Fraction _ | Float _ | Bitvector _ as v ->
      cannot_import "not implemented for value %a" print_model_const_human v

(** Import a value from the prover model to an interpreter value.

    @raise Exit when the type [ity] and the shape of the the value [v] do not
    match. This may happen when a module that contains a value with an abstract
    type is cloned with different types as instantiations of the abstract type.

    @raise CannotImportModelValue when the value cannot be imported *)
let rec import_model_value check known th_known ity v =
  let ts, l1, l2 = ity_components ity in
  let subst = its_match_regs ts l1 l2 in
  let def = Pdecl.find_its_defn known ts in
  let res = match v with
      | Const c -> import_model_const ity c
      | Var _ -> undefined_value ity
      | Record r ->
          let rs = match def.Pdecl.itd_constructors with [rs] -> rs | _ ->
            cannot_import "type with not exactly one constructors" in
          let aux field_rs =
            let field_name = trace_or_name field_rs.rs_name in
            let field_ity = ity_full_inst subst (fd_of_rs field_rs).pv_ity in
            match List.assoc field_name r with
            | v -> import_model_value check known th_known field_ity v
            | exception Not_found ->
                (* TODO Better create a default value? Requires an [Env.env]. *)
                undefined_value field_ity in
          let vs = List.map aux def.Pdecl.itd_fields in
          constr_value ity rs def.Pdecl.itd_fields vs
      | Apply (s, vs) ->
          let matching_name rs = String.equal rs.rs_name.id_string s in
          let rs = List.find matching_name def.Pdecl.itd_constructors in
          let itys = List.map (fun pv -> ity_full_inst subst pv.pv_ity)
              rs.rs_cty.cty_args in
          let vs = List.map2 (import_model_value check known th_known) itys vs in
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
          let x = import_model_value check known th_known (ity_of_ty ty_res) x in
          proj_value ity ls x
      | Array a ->
          let open Ty in
          if not (its_equal def.Pdecl.itd_its its_func) then
            cannot_import "Cannot import array as %a" print_its def.Pdecl.itd_its;
          let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
            | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
            | _ -> assert false in
          let key_value ix = ix.arr_index_key, ix.arr_index_value in
          let keys, values = List.split (List.map key_value a.arr_indices) in
          let keys = List.map (import_model_value check known th_known key_ity) keys in
          let values = List.map (import_model_value check known th_known value_ity) values in
          let mv = Mv.of_list (List.combine keys values) in
          let v0 = import_model_value check known th_known value_ity a.arr_others in
          purefun_value ~result_ity:ity ~arg_ity:key_ity mv v0
      | Unparsed s -> cannot_import "unparsed value %s" s
      | Undefined -> undefined_value ity in
  check ity res;
  res

let get_value m known th_known =
  fun ?loc check id ity ->
  match search_model_element_for_id m ?loc id with
  | me -> Some (import_model_value check known th_known ity me.me_value)
  | exception Not_found -> None

(** Check and select solver counterexample models *)

(** Identifies the rsymbol of the definition that contains the given
   position. *)
let find_rs_by_loc pm loc =
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
         Opt.exists in_e td.itd_witness in
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

let check_model_rs ?timelimit ?steplimit ~abstract reduce env pm model rs =
  Debug.dprintf debug_check_ce "%s-step RAC@."
    (if abstract then "Giant" else "Small");
  let {Pmodule.mod_known; mod_theory= {Theory.th_known}} = pm in
  let get_value = get_value model mod_known th_known in
  let rac = rac_config ~do_rac:true ~abstract ?timelimit ?steplimit
      ~skip_cannot_compute:false ~reduce ~get_value () in
  let print_oloc =
    Pp.print_option_or_default "unknown location" Pretty.print_loc' in
  try
    let _, env = eval_rs rac env pm rs in
    let reason = "no contradiction during execution" in
    {state= Rnormal; reason; exec_log= Log.close_log env.rac.log_uc}
  with
  | Contr (ctx, t) ->
      let reason = "contradiction encountered" in
      {state= Rfailure (ctx, t); reason; exec_log= Log.close_log ctx.c_log_uc}
  | RACStuck (env,l,reason) ->
      let reason = asprintf "%s at %a" reason print_oloc l in
      {state= Rstuck; reason; exec_log= Log.close_log env.rac.log_uc}
  | CannotImportModelValue msg ->
      let reason =
        sprintf "cannot import value from model: %s" msg in
      {state= Runknown; reason; exec_log= Log.empty_log}
  | CannotCompute r ->
      let reason = sprintf "terminated because %s" r.reason in
      {state= Runknown; reason; exec_log= Log.empty_log}

let find_rs pm model =
  match get_model_term_loc model with
  | None -> failwith "model term has no location"
  | Some vc_term_loc ->
      (* TODO deal with VCs from goal definitions? *)
      if Loc.equal vc_term_loc Loc.dummy_position then
        failwith ("Pinterp.check_model: the term of the CE model has a \
                   dummy location, it cannot be used to find the \
                   toplevel definition");
      match find_rs_by_loc pm vc_term_loc with
      | None ->
          Format.kasprintf failwith "no corresponding routine symbol found for %a"
            Pretty.print_loc' vc_term_loc
      | Some rs -> rs

let check_model ?timelimit ?steplimit reduce env pm model =
  match find_rs pm model with
  | exception Failure reason -> Cannot_check_model {reason}
  | rs ->
      let me_name_trans men = men.Model_parser.men_name in
      let print_attrs = Debug.test_flag Call_provers.debug_attrs in
      Debug.dprintf debug_check_ce
        "@[Checking model:@\n@[<hv2>%a@]@]@\n"
        (print_model ~filter_similar:false ~me_name_trans ~print_attrs) model;
      let check_model_rs ~abstract =
        check_model_rs ~abstract ?timelimit ?steplimit reduce env pm model rs in
      let abstract = check_model_rs ~abstract:true in
      let concrete = check_model_rs ~abstract:false in
      Check_model_result {concrete; abstract}

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
      | NC _ | SW _ | NCSW _ -> true
      | BAD _ | UNKNOWN _ -> false in
    List.partition is_good models in
  if good_models = [] then
    (* No good models. Prioritize the last, non-empty model as it was done
       before 2020, but penalize bad models. *)
    let ce_summary_index = function
      | UNKNOWN _ -> 0 | BAD _ -> 1
      | NC _ | SW _ | NCSW _ -> assert false in
    let compare = cmp [
        cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
        cmptr (fun (i,_,_,_,_) -> -i) (-);
      ] in
    let not_empty (_,_,m,_,_) = not (Model_parser.is_model_empty m) in
    List.sort compare (List.filter not_empty other_models)
  else
    let ce_summary_index = function
      | NC _ -> 0 | SW _ -> 1 | NCSW _ -> 2
      | UNKNOWN _ | BAD _ -> assert false in
    let compare = cmp [
        (* prefer NC > SW > NCSW > UNKNOWN > BAD *)
        cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
        (* prefer simpler models *)
        cmptr (fun (i,_,_,_,_) -> i) (-);
      ] in
    List.sort compare good_models

let print_dbg_model selected_ix fmt (i,_,_,mr,s) =
  let mark_selected fmt =
    Pp.string fmt (if selected_ix = Some i then "Selected" else "Checked") in
  fprintf fmt "- @[<v>%t model %d: %a@]" mark_selected i
    (print_result_summary print_result) (mr, s)

let select_model ?verb_lvl ?(check=false) ?(reduce_config=rac_reduce_config ())
    ?timelimit ?steplimit ?sort_models env pmodule models =
  let sort_models = Opt.get_def
      (if check then prioritize_first_good_model
       else prioritize_last_non_empty_model) sort_models in
  let check_model =
    if check then check_model ?timelimit ?steplimit reduce_config env pmodule
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
      let vc_term_loc = get_model_term_loc m in
      let vc_term_attrs = get_model_term_attrs m in
      let s = ce_summary ~vc_term_loc ~vc_term_attrs mr in
      Debug.dprintf debug_check_ce "@[<v2>Result of checking model %d: %a@]@." i
        (print_check_model_result ?verb_lvl) (mr, s);
      i,r,m,mr,s in
    List.map add_check_model_result models in
  let selected, selected_ix =
    match List.nth_opt (sort_models models) 0 with
    | None -> None, None
    | Some (i,_,m,_,s) -> Some (m, s), Some i in
  if models <> [] then
    Debug.dprintf debug_check_ce_summary "Results:@ %a@."
      Pp.(print_list newline (print_dbg_model selected_ix)) models;
  selected

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
      | me -> me.me_name.men_kind
      | exception Not_found -> Other in
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
