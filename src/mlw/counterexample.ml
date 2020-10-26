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

open Term
open Ity
open Expr
open Format
open Pinterp

let debug_check_ce = Debug.register_info_flag "check-ce"
    ~desc:"Debug@ info@ for@ --check-ce"

(** Identifies the rsymbol of the definition that contains the given position. **)
let find_rs pm loc =
  let open Pmodule in
  let open Pdecl in
  let rec find_in_list f = function
    | [] -> None
    | x :: xs -> match f x with
      | None -> find_in_list f xs
      | res -> res in
  let in_t t =
    Opt.equal Loc.equal (Some loc) t.t_loc ||
    t_any (fun t ->  Opt.equal Loc.equal (Some loc) t.t_loc) t in
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
          if in_tdef td then Warning.emit "Can't check CE for VC from type definitions :(";
          None in
        find_in_list find_td ds
    | PDlet ld ->
        (match ld with
         | LDvar (_, e) -> (* TODO *)
             if in_e e then Warning.emit "Can't check CE for VC from variable definitions :(";
             None
         | LDsym (rs, ce) ->
             maybe (in_cty rs.rs_cty || in_ce ce) rs
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

let check_model reduce env pm model =
  let open Model_parser in
  match get_model_term_loc model with
  | None ->
      let reason = "model term has no location" in
      Cannot_check_model {reason}
  | Some loc ->
      (* TODO deal with VCs from goal definitions? *)
      if Loc.equal loc Loc.dummy_position then
        failwith ("Pinterp.check_model: the term of the CE model has a dummy "^
                  "location, it cannot be used to find the toplevel definition");
      match find_rs pm loc with
      | Some rs ->
          let check_model_rs ~abstract =
            let rac = rac_config ~do_rac:true ~abstract ~reduce ~model () in
            check_model_rs rac env pm model rs in
          let concrete = check_model_rs ~abstract:false in
          let abstract = check_model_rs ~abstract:true in
          Check_model_result {concrete; abstract}
      | None ->
          let reason =
            Format.asprintf "no corresponding routine symbol found for %a"
              Pretty.print_loc' loc in
          Cannot_check_model {reason}

(** See output of [ce_summary_title] for details *)

type ce_summary = NCCE of exec_log | SWCE of exec_log
                  | NCCE_SWCE of exec_log | BAD_CE | UNKNOWN of string

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
        ("The@ program@ does@ not@ comply@ to@ the@ verification@ goal,@ "^^
         "or@ the@ contracts@ of@ some@ loop@ or@ function@ are@ too@ weak")
  | BAD_CE ->
      Format.fprintf fmt
        "Sorry,@ we@ don't@ have@ a@ good@ counterexample@ for@ you@ :("
  | UNKNOWN reason ->
      match check_ce with
      | Some true ->
          fprintf fmt
            "The@ following@ counterexample@ model@ could@ not@ be@ verified@ (%s)"
            reason
      | Some false ->
          fprintf fmt
            ("The@ following@ counterexample@ model@ has@ not@ been@ verified@ "^^
             "(%s,@ missing@ option@ --check-ce)") reason
      | None ->
          fprintf fmt "The@ following@ counterexample@ model@ has@ not@ been@ verified@ (%s)"
            reason

let print_ce_summary_values ~json ~print_attrs model fmt s =
  let open Json_base in
  let print_model_field =
    print_json_field "model" (Model_parser.print_model_json ?me_name_trans:None ~vc_line_trans:string_of_int) in
  let print_log_field =
    print_json_field "log" (print_exec_log ~json:true) in
  match s with
  | NCCE log | SWCE log | NCCE_SWCE log ->
      if json then
        fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
          print_model_field model print_log_field log
      else
        fprintf fmt "@[%a@]" (print_exec_log ~json:false) log
  | UNKNOWN _ ->
      if json then
        fprintf fmt "@[@[<hv1>{%a@]}@]" print_model_field model
      else
        fprintf fmt "@[%a@]" (Model_parser.print_model_human ?me_name_trans:None ~print_attrs) model
  | BAD_CE -> ()

let sort_exec_log log =
  let open Wstdlib in
  let insert f l e sofar =
    let insert_line opt_l =
      let l = Opt.get_def [] opt_l in
      Some (e :: l) in
    let insert_file opt_mf =
      let mf = Opt.get_def Mint.empty opt_mf in
      let res = Mint.change insert_line l mf in
      Some res in
    Mstr.change insert_file f sofar in
  let aux entry sofar = match entry.log_loc with
    | Some loc when not (Loc.equal loc Loc.dummy_position) ->
        let f, l, _, _ = Loc.get loc in
        insert f l entry sofar
    | _ -> sofar in
  Mstr.map (Mint.map List.rev)
    (List.fold_right aux log Mstr.empty)

let model_of_exec_log ~original_model ?(valid_loc=(fun loc -> not (Loc.equal loc Loc.dummy_position))) log =
  let open Model_parser in
  let open Ident in
  let open Wstdlib in
  let me loc id v =
    let name = asprintf "%a" Ident.print_decoded id.id_string in
    let men_name = Ident.get_model_trace_string ~name ~attrs:id.Ident.id_attrs in
    let men_kind = match get_model_element_by_id original_model id with
      | Some me -> me.me_name.men_kind
      | None -> Other in
    let me_name = { men_name; men_kind; men_attrs= id.id_attrs } in
    let me_value = Integer v in (* TODO Type me_value correctly when the exec log is typed *)
    {me_name; me_value; me_location= Some loc; me_term= None} in
  let aux e = match e.log_loc with
    | Some loc when valid_loc loc -> (
        match e.log_desc with
        | Val_from_model (id, v) ->
            [me loc id v]
        | Exec_failed (_, mid) ->
            Mid.fold (fun id v l -> me loc id v :: l) mid []
        | _ -> [] )
    | _ -> [] in
  let aux_l e = match List.concat (List.map aux e) with [] -> None | l -> Some l in
  let aux_mint mint =
    let res = Mint.map_filter aux_l mint in
    if Mint.is_empty res then None else Some res in
  let model_files = (Mstr.map_filter aux_mint (sort_exec_log log)) in
  set_model_files original_model model_files

let model_of_ce_summary ~original_model ?valid_loc = function
  | NCCE log | SWCE log | NCCE_SWCE log ->
      model_of_exec_log ~original_model ?valid_loc (log_to_list log)
  | UNKNOWN _ | BAD_CE -> original_model

let ce_summary v_concrete v_abstract =
  let open Model_parser in
  match v_concrete.verdict, v_abstract.verdict with
  | Good_model, _ -> NCCE v_concrete.exec_log
  | Bad_model, Good_model -> SWCE v_abstract.exec_log
  | Dont_know, Good_model -> NCCE_SWCE v_abstract.exec_log
  | Dont_know, Dont_know
  | Dont_know, Bad_model -> UNKNOWN v_concrete.reason
  | Bad_model, Dont_know -> UNKNOWN v_abstract.reason
  | Bad_model, Bad_model -> BAD_CE

let print_counterexample ?check_ce ?(json=false) fmt (model,ce_summary) =
  if not (Model_parser.is_model_empty model) then
    fprintf fmt "@ @[<hov2>%a%t@]" (print_ce_summary_title ?check_ce) ce_summary
      (fun fmt -> match ce_summary with
                  | NCCE _ | SWCE _ | NCCE_SWCE _ ->
                     fprintf fmt ",@ for@ example@ during@ the@ following@ execution:"
                  | UNKNOWN _ ->
                     fprintf fmt ":"
                  | _ -> ());
  fprintf fmt "@ %a" (print_ce_summary_values ~print_attrs:false ~json model)
    ce_summary

let select_model ?(check=false) rac_reduce_config env pmodule models =
  let default_check_model _ =
    let reason = "not checking CE model" in
    Cannot_check_model {reason} in
  let check_model =
    if check then check_model rac_reduce_config env pmodule
    else default_check_model in
  let check_model (i,r,m) =
    Debug.dprintf debug_check_ce "Check model %d (%a)@." i
      (Pp.print_option_or_default "NO LOC" Pretty.print_loc') (Model_parser.get_model_term_loc m);
    (* Debug.dprintf debug_check_ce "@[<hv2>Model from prover:@\n@[%a@]@]@."
     *   (print_model ?me_name_trans:None ~print_attrs:false) m; *)
    let mr = check_model m in
    Debug.dprintf debug_check_ce "@[<v2>Model %d:@\n@[%a@]@]@." i
      print_check_model_result mr;
    i,r,m,mr in
  let not_empty (i,_,m) =
    let empty = Model_parser.is_model_empty m in
    if empty then Debug.dprintf debug_check_ce "Model %d is empty@." i;
    not empty in
  let add_ce_summary (i,r,m,mr) =
    let summary = match mr with
      | Cannot_check_model {reason} -> UNKNOWN reason
      | Check_model_result r -> ce_summary r.concrete r.abstract in
    i,r,m,mr,summary in
  let models =
    List.map add_ce_summary
      (List.map check_model
         (List.filter not_empty
            (List.mapi (fun i (r,m) -> i,r,m)
               models))) in
  let is_good (_,_,_,_,s) = match s with NCCE _ | SWCE _ | NCCE_SWCE _ -> true | BAD_CE | UNKNOWN _ -> false in
  let good_models, other_models = List.partition is_good models in
  let model_infos =
    let open Util in
    if good_models <> [] then
      let ce_summary_index = function
        | NCCE _ -> 0 | SWCE _ -> 1 | NCCE_SWCE _ -> 2 | UNKNOWN _ | BAD_CE -> assert false in
      let compare = cmp [
          (* prefer NCCE > SWCE > NCCE_SWCE > UNKNOWN > BAD *)
          cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
          (* prefer simpler models *)
          cmptr (fun (i,_,_,_,_) -> i) (-);
        ] in
      List.sort compare good_models
    else
      (* No interesting models, so choose the most complex (later) model
         as it was done before 2020, but penalize bad models. *)
      let ce_summary_index = function
        UNKNOWN _ -> 0 | BAD_CE -> 1 | NCCE _ | SWCE _ | NCCE_SWCE _ -> assert false in
      let compare = cmp [
          cmptr (fun (_,_,_,_,s) -> ce_summary_index s) (-);
          cmptr (fun (i,_,_,_,_) -> -i) (-);
        ] in
      List.sort compare other_models in
  let selected_ix, selected = match model_infos with
    | [] -> None, None
    | (i,_,m,_,s) :: _ -> Some i, Some (m, s) in
  let print_dbg_model fmt (i,_,_,mr,s) =
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
         (print_ce_summary_title ?check_ce:None) s in
  if models <> [] then
    Debug.dprintf debug_check_ce "Models:@\n%a@."
      Pp.(print_list space print_dbg_model) models;
  selected
