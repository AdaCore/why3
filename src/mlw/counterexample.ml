open Term
open Ity
open Expr
open Pinterp

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
  match Model_parser.get_model_term_loc model with
  | None ->
      let reason = "model term has no location" in
      Model_parser.Cannot_check_model {reason}
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

