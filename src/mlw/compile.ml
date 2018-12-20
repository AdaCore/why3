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

(*
  - "use (im|ex)port" -> "open"
    but OCaml's open is not transitive, so requires some extra work
    to figure out all the opens

  - if a WhyML module M is extracted to something that is a signature,
    then extract "module type B_sig = ..." (as well as "module B = ...")
*)

(** Abstract syntax of ML *)

open Ident
open Ity
open Ty
open Term

let clean_name fname =
  (* TODO: replace with Filename.remove_extension
   * after migration to OCaml 4.04+ *)
  let remove_extension s =
    try Filename.chop_extension s with Invalid_argument _ -> s in
  let f = Filename.basename fname in (remove_extension f)

let module_name ?fname path t =
  let fname = match fname, path with
    | None, "why3"::_ -> "why3"
    | None, _   -> String.concat "__" path
    | Some f, _ -> clean_name f in
  fname ^ "__" ^ t

(** Translation from Mlw to ML *)

module Translate = struct

  open Expr
  open Pmodule
  open Pdecl

  module ML = Mltree

  let ht_rs = Hrs.create 7 (* rec_rsym -> rec_sym *)

  let debug_compile =
    Debug.register_info_flag ~desc:"Compilation" "compile"

  (* useful predicates and transformations *)
  let pv_not_ghost e = not e.pv_ghost

  (* remove ghost components from tuple, using mask *)
  (* TODO : completely remove this function *)
  let visible_of_mask m sl = match m with
    | MaskGhost    -> assert false (* FIXME ? *)
    | MaskVisible  -> sl
    | MaskTuple ml ->
        let add_ity acc m ity = if mask_ghost m then acc else ity :: acc in
        if List.length sl < List.length ml then sl (* FIXME ? much likely... *)
        else List.rev (List.fold_left2 add_ity [] ml sl)

  (* types *)
  let rec type_ ty =
    match ty.ty_node with
    | Tyvar tvs ->
        ML.Tvar tvs
    | Tyapp (ts, tyl) when is_ts_tuple ts ->
        ML.Ttuple (List.map type_ tyl)
    | Tyapp (ts, tyl) ->
        ML.Tapp (ts.ts_name, List.map type_ tyl)

  let vsty vs =
    vs.vs_name, type_ vs.vs_ty

  let rec filter_ghost_params p def = function
    | [] -> []
    | pv :: l ->
        if p pv then def pv :: (filter_ghost_params p def l)
        else filter_ghost_params p def l

  let rec filter_out_ghost_rdef = function
    | [] -> []
    | { rec_sym = rs; rec_rsym = rrs } :: l when rs_ghost rs || rs_ghost rrs ->
        filter_out_ghost_rdef l
    | rdef :: l ->
        rdef :: filter_out_ghost_rdef l

  let rec pat m p = match p.pat_node with
    | Pwild ->
        ML.Pwild
    | Pvar vs when (restore_pv vs).pv_ghost ->
        ML.Pwild
    | Pvar vs ->
        ML.Pvar vs
    | Por (p1, p2) ->
        ML.Por (pat m p1, pat m p2)
    | Pas (p, vs) when (restore_pv vs).pv_ghost ->
        pat m p
    | Pas (p, vs) ->
        ML.Pas (pat m p, vs)
    | Papp (ls, pl) when is_fs_tuple ls ->
        let pl = visible_of_mask m pl in
        begin match pl with
          | [] -> ML.Pwild
          | [p] -> pat m p
          | _ -> ML.Ptuple (List.map (pat m) pl) end
    | Papp (ls, pl) ->
        let rs = restore_rs ls in
        let args = rs.rs_cty.cty_args in
        let mk acc pv pp = if not pv.pv_ghost then pat m pp :: acc else acc in
        let pat_pl = List.fold_left2 mk [] args pl in
        ML.Papp (ls, List.rev pat_pl)

  (** programs *)

  let pv_name pv = pv.pv_vs.vs_name

  (* individual types *)
  let mlty_of_ity mask t =
    let rec loop t = match t.ity_node with
      | _ when mask_equal mask MaskGhost -> ML.tunit
      | Ityvar tvs ->
          ML.Tvar tvs
      | Ityapp ({its_ts = ts}, itl, _) when is_ts_tuple ts ->
          let itl = visible_of_mask mask itl in
          ML.Ttuple (List.map loop itl)
      | Ityapp ({its_ts = ts}, itl, _) ->
          ML.Tapp (ts.ts_name, List.map loop itl)
      | Ityreg {reg_its = its; reg_args = args} ->
          let args = List.map loop args in
          ML.Tapp (its.its_ts.ts_name, args) in
    loop t

  let pvty pv =
    if pv.pv_ghost then ML.mk_var (pv_name pv) ML.tunit true
    else let (vs, vs_ty) = vsty pv.pv_vs in ML.mk_var vs vs_ty false

  let for_direction = function
    | To -> ML.To
    | DownTo -> ML.DownTo

  let isconstructor info rs = (* TODO *)
    match Mid.find_opt rs.rs_name info.ML.from_km with
    | Some {pd_node = PDtype its} ->
        let is_constructor its =
          List.exists (rs_equal rs) its.itd_constructors in
        List.exists is_constructor its
    | _ -> false

  let is_singleton_imutable itd =
    let not_g e = not (rs_ghost e) in
    let pjl = itd.itd_fields in
    let mfields = itd.itd_its.its_mfields in
    let pv_equal_field rs = pv_equal (fd_of_rs rs) in
    let get_mutable rs = List.exists (pv_equal_field rs) mfields in
    match filter_ghost_params not_g get_mutable pjl with
    | [is_mutable] -> not is_mutable
    | _ -> false

  let get_record_itd info rs =
    match Mid.find_opt rs.rs_name info.ML.from_km with
    | Some {pd_node = PDtype itdl} ->
        let f pjl_constr = List.exists (rs_equal rs) pjl_constr in
        let itd = match rs.rs_field with
          | Some _ -> List.find (fun itd -> f itd.itd_fields) itdl
          | None -> List.find (fun itd -> f itd.itd_constructors) itdl in
        if itd.itd_fields = [] then None else Some itd
    | _ -> None

  let is_optimizable_record_itd itd =
    not itd.itd_its.its_private && is_singleton_imutable itd

  let is_optimizable_record_rs info rs =
    Opt.fold (fun _ -> is_optimizable_record_itd) false (get_record_itd info rs)

  let is_empty_record_itd itd =
    let is_ghost rs = rs_ghost rs in
    List.for_all is_ghost itd.itd_fields

  let is_empty_record info rs =
    Opt.fold (fun _ -> is_empty_record_itd) false (get_record_itd info rs)

  let mk_eta_expansion rs pvl ({cty_args = ca; cty_effect = ce} as c) =
    (* FIXME : effects and types of the expression in this situation *)
    let rs = Hrs.find_def ht_rs rs rs in
    let mv = MaskVisible in
    let args_f =
      let def pv =
        pv_name pv, mlty_of_ity (mask_of_pv pv) pv.pv_ity, pv.pv_ghost in
      filter_ghost_params pv_not_ghost def ca in
    let args =
      let def pv = ML.mk_expr (ML.Evar pv) (ML.I pv.pv_ity) mv
        eff_empty Sattr.empty in
      let args = filter_ghost_params pv_not_ghost def pvl in
      let extra_args = List.map def ca in args @ extra_args in
    let eapp = ML.mk_expr (ML.Eapp (rs, args)) (ML.C c) mv
      ce Sattr.empty in
    ML.mk_expr (ML.Efun (args_f, eapp)) (ML.C c) mv ce Sattr.empty

  (* function arguments *)
  let filter_params args =
    let args = List.map pvty args in
    let p (_, _, is_ghost) = not is_ghost in
    List.filter p args

  let params args = let args = filter_params args in
    if args = [] then [ML.mk_var_unit] else args

  let filter_params_cty p def pvl cty_args =
    let rec loop = function
      | [], _ -> []
      | pv :: l1, arg :: l2 ->
          if p pv && p arg then def pv :: loop (l1, l2) else loop (l1, l2)
      | _ -> assert false
    in loop (pvl, cty_args)

  let app pvl cty_args f_zero =
    let def pv = ML.mk_expr (ML.Evar pv) (ML.I pv.pv_ity) MaskVisible
      eff_empty Sattr.empty in
    let args = filter_params_cty pv_not_ghost def pvl cty_args in
    f_zero args

  (* build the set of type variables from functions arguments *)
  let rec add_tvar acc = function
    | ML.Tvar tv -> Stv.add tv acc
    | ML.Tapp (_, tyl) | ML.Ttuple tyl ->
        List.fold_left add_tvar acc tyl

  (* expressions *)
  let rec expr info svar mask ({e_effect = eff; e_attrs = attrs} as e) =
    assert (not (e_ghost e));
    assert (not (mask_spill e.e_mask mask));
    let pv_list_of_mask pvl mask =
      let mk_pv_of_mask acc pv = function MaskGhost -> acc | _ -> pv :: acc in
      match mask with
      | MaskGhost   -> []
      | MaskVisible -> pvl
      | MaskTuple m -> assert (List.length m = List.length pvl);
          let pvl = List.fold_left2 mk_pv_of_mask [] pvl m in
          List.rev pvl in
    match e.e_node with
    | Econst _ | Evar _ when mask = MaskGhost ->
        ML.e_unit
    | Eexec ({c_node = Cfun _; c_cty = {cty_args}}, _)
      when cty_args <> [] && mask = MaskGhost ->
        ML.e_unit
    | Eexec ({c_node = Capp (rs, _)}, _)
      when isconstructor info rs && mask = MaskGhost ->
        ML.e_unit
    | Econst c -> Debug.dprintf debug_compile "compiling constant@.";
        assert (mask = MaskVisible);
        let c = match c with Number.ConstInt c -> c | _ -> assert false in
        ML.e_const c (ML.I e.e_ity) mask eff attrs
    | Evar pv ->
        Debug.dprintf debug_compile "compiling variable %a@." print_pv pv;
        assert (mask = MaskVisible);
        ML.e_var pv (ML.I e.e_ity) mask eff attrs
    | Elet (LDvar (_, e1), e2) when e_ghost e1 ->
        expr info svar mask e2
    | Elet (LDvar (_, e1), e2) when e_ghost e2 ->
        (* sequences are transformed into [let o = e1 in e2] by A-normal form *)
        expr info svar MaskGhost e1
    | Elet (LDvar (pv, e1), e2)
      when pv.pv_ghost || not (Mpv.mem pv e2.e_effect.eff_reads) ->
        if eff_pure e1.e_effect then expr info svar mask e2
        else let e1 = ML.e_ignore e1.e_ity (expr info svar MaskGhost e1) in
          ML.e_seq e1 (expr info svar mask e2) (ML.I e.e_ity) mask eff attrs
    | Elet (LDvar (pv, e1), e2) ->
        Debug.dprintf debug_compile "compiling local definition of %s@."
          (pv_name pv).id_string;
        let ld = ML.var_defn pv (expr info svar MaskVisible e1) in
        ML.e_let ld (expr info svar mask e2) (ML.I e.e_ity) mask eff attrs
    | Elet (LDsym (rs, _), ein) when rs_ghost rs ->
        expr info svar mask ein
    | Elet (LDsym (_, {c_node = Cpur (_, _); _}), _) ->
        assert false (* necessarily handled above *)
    | Elet (LDsym (rs, {c_node = Cfun ef; c_cty = cty}), ein) ->
        Debug.dprintf debug_compile "compiling local function definition %s@."
          rs.rs_name.id_string;
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let ld = ML.sym_defn rs res args (expr info svar cty.cty_mask ef) in
        ML.e_let ld (expr info svar mask ein) (ML.I e.e_ity) mask eff attrs
    | Elet (LDsym (rs, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein)
      when isconstructor info rs_app -> (* partial application of constructor *)
        let eta_app = mk_eta_expansion rs_app pvl cty in
        let mk_func pv f = ity_func pv.pv_ity f in
        let func = List.fold_right mk_func cty.cty_args cty.cty_result in
        let res = mlty_of_ity cty.cty_mask func in
        let ld = ML.sym_defn rs res [] eta_app in
        let ein = expr info svar mask ein in
        ML.e_let ld ein (ML.I e.e_ity) mask eff attrs
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein) ->
        (* partial application *) (* FIXME -> zero arguments functions *)
        Debug.dprintf debug_compile "compiling partial application of %s@."
          rsf.rs_name.id_string;
        let cmk = cty.cty_mask in
        let ceff = cty.cty_effect in
        let pvl = app pvl rs_app.rs_cty.cty_args (fun x -> x) in
        let rs_app = Hrs.find_def ht_rs rs_app rs_app in
        let eapp = ML.e_app rs_app pvl (ML.C cty) cmk ceff Sattr.empty in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let ld = ML.sym_defn rsf res (params cty.cty_args) eapp in
        let ein = expr info svar mask ein in
        ML.e_let ld ein (ML.I e.e_ity) mask eff attrs
    | Elet (LDsym (_, {c_node = Cany; _}), _) -> let loc = e.e_loc in
        Loc.errorm ?loc "This expression cannot be extracted"
    | Elet (LDrec rdefl, ein) ->
        let rdefl = filter_out_ghost_rdef rdefl in
        List.iter
          (fun { rec_sym = rs1; rec_rsym = rs2; } ->
            Hrs.replace ht_rs rs2 rs1) rdefl;
        let def = function
          | { rec_sym = rs1; rec_fun = {c_node = Cfun ef; c_cty = cty} } ->
              let res = mlty_of_ity rs1.rs_cty.cty_mask rs1.rs_cty.cty_result in
              let args = params cty.cty_args in
              let new_svar =
                let args' = List.map (fun (_, ty, _) -> ty) args in
                let svar  = List.fold_left add_tvar Stv.empty args' in
                add_tvar svar res in
              let new_svar = Stv.diff new_svar svar in
              let ef = expr info (Stv.union svar new_svar) ef.e_mask ef in
              { ML.rec_sym  = rs1; ML.rec_args = args; ML.rec_exp  = ef;
                ML.rec_res  = res; ML.rec_svar = new_svar; }
          | _ -> assert false in
        let rdefl = List.map def rdefl in
        if rdefl <> [] then
          let ein = expr info svar mask ein in
          let ml_letrec = ML.Elet (ML.Lrec rdefl, ein) in
          ML.mk_expr ml_letrec (ML.I e.e_ity) mask e.e_effect attrs
        else expr info svar mask ein
    | Eexec ({c_node = Capp (rs, [])}, _)  when is_rs_tuple rs ->
        ML.e_unit
    | Eexec ({c_node = Capp (rs, pvl)}, _) when is_rs_tuple rs ->
        let pvl = pv_list_of_mask pvl mask in
        let res_ity = ity_tuple (List.map (fun v -> v.pv_ity) pvl) in
        let pvl = ML.var_list_of_pv_list pvl in
        ML.e_app rs pvl (ML.I res_ity) mask eff attrs
    | Eexec ({c_node = Capp (rs, _)}, _) when is_empty_record info rs ->
        ML.e_unit
    | Eexec ({c_node = Capp (rs, pvl); c_cty = cty}, _)
      when isconstructor info rs && cty.cty_args <> [] ->
        (* partial application of constructors *)
        mk_eta_expansion rs pvl cty
    | Eexec ({c_node = Capp (rs, pvl); c_cty = cty}, _) ->
        Debug.dprintf debug_compile "compiling total application of %s@."
          rs.rs_name.id_string;
        Debug.dprintf debug_compile "cty_args: %d@." (List.length cty.cty_args);
        let rs = Hrs.find_def ht_rs rs rs in
        let add_unit = function [] -> [ML.e_unit] | args -> args in
        let id_f = fun x -> x in
        let f_zero = match rs.rs_logic with RLnone ->
          Debug.dprintf debug_compile "it is a RLnone@."; add_unit
                                          | _ -> id_f in
        let pvl = app pvl rs.rs_cty.cty_args f_zero in
        begin match pvl with
          | [pv_expr] when is_optimizable_record_rs info rs -> pv_expr
          | _ -> ML.e_app rs pvl (ML.I e.e_ity) mask eff attrs end
    | Eexec ({c_node = Cfun e; c_cty = {cty_args = []}}, _) ->
        (* abstract block *)
        Debug.dprintf debug_compile "compiling abstract block@.";
        expr info svar mask e
    | Eexec ({c_node = Cfun ef; c_cty = cty}, _) ->
        (* is it the case that every argument here is non-ghost ? *)
        Debug.dprintf debug_compile "compiling a lambda expression@.";
        let ef = expr info svar e.e_mask ef in
        ML.e_fun (params cty.cty_args) ef (ML.I e.e_ity) mask eff attrs
    | Eexec ({c_node = Cpur (_, _); _ }, _) ->
        assert false (* necessarily ghost *)
    | Eexec ({c_node = Cany}, _) -> let loc = e.e_loc in
        Loc.errorm ?loc "This expression cannot be extracted"
    | Eabsurd ->
        ML.e_absurd (ML.I e.e_ity) mask eff attrs
    | Eassert _ ->
        ML.e_unit
    | Eif (e1, e2, e3) when e_ghost e1 ->
        (* if [e1] is ghost but the entire [if-then-else] expression doesn't,
           it must be the case one of the branches is [Eabsurd] *)
        if e2.e_node = Eabsurd then expr info svar mask e3
        else expr info svar mask e2
    | Eif (e1, e2, e3) when e_ghost e3 ->
        let e1 = expr info svar e1.e_mask e1 in
        let e2 = expr info svar mask e2 in
        ML.e_if e1 e2 ML.e_unit mask eff attrs
    | Eif (e1, e2, e3) when e_ghost e2 ->
        let e1 = expr info svar e1.e_mask e1 in
        let e3 = expr info svar mask e3 in
        ML.e_if e1 ML.e_unit e3 mask eff attrs
    | Eif (e1, e2, e3) -> Debug.dprintf debug_compile "compiling if block@.";
        let e1 = expr info svar e1.e_mask e1 in
        let e2 = expr info svar mask e2 in
        let e3 = expr info svar mask e3 in
        ML.e_if e1 e2 e3 mask eff attrs
    | Ewhile (e1, _, _, e2) ->
        Debug.dprintf debug_compile "compiling while block@.";
        let e1 = expr info svar e1.e_mask e1 in
        let e2 = expr info svar e2.e_mask e2 in
        ML.e_while e1 e2 mask eff attrs
    | Efor (pv1, (pv2, dir, pv3), _, _, efor) ->
        Debug.dprintf debug_compile "compiling for block@.";
        let dir = for_direction dir in
        let efor = expr info svar efor.e_mask efor in
        ML.e_for pv1 pv2 dir pv3 efor mask eff attrs
    | Eghost _ | Epure _ ->
        assert false
    | Eassign al ->
        let rm_ghost (_, rs, _) = not (rs_ghost rs) in
        let al = List.filter rm_ghost al in
        let e_of_var pv = ML.e_var pv (ML.I pv.pv_ity) MaskVisible eff attrs in
        let al = List.map (fun (pv1, rs, pv2) -> (pv1, rs, e_of_var pv2)) al in
        ML.e_assign al (ML.I e.e_ity) mask eff attrs
    | Ematch (e1, bl, xl) when e_ghost e1 ->
        assert (Mxs.is_empty xl); (* Expr ensures this for the time being *)
        (* if [e1] is ghost but the entire [match-with] expression isn't,
           it must be the case the first non-absurd branch is irrefutable *)
        (match bl with (* FIXME: skip absurd branches *)
         | [] -> assert false | (_, e) :: _ -> expr info svar e.e_mask e)
    | Ematch (e1, [], xl) when Mxs.is_empty xl ->
        expr info svar e1.e_mask e1
    | Ematch (e1, bl, xl) ->
        let e1, bl = match bl with
          | [] -> expr info svar mask e1, []
          | bl -> let bl = List.map (ebranch info svar mask) bl in
              expr info svar e1.e_mask e1, bl in
        let mk_xl (xs, (pvl, e)) = let pvl = pv_list_of_mask pvl xs.xs_mask in
          if e.e_effect.eff_ghost then (xs, pvl, ML.e_unit)
          else (xs, pvl, expr info svar mask e) in
        let xl = List.map mk_xl (Mxs.bindings xl) in
        ML.e_match e1 bl xl (ML.I e.e_ity) mask eff attrs
    | Eraise (xs, ex) -> let ex = match expr info svar xs.xs_mask ex with
        | {ML.e_node = ML.Eblock []} -> None
        | e -> Some e in
        ML.mk_expr (ML.Eraise (xs, ex)) (ML.I e.e_ity) mask eff attrs
    | Eexn (xs, e1) ->
        if mask_ghost e1.e_mask then ML.mk_expr
          (ML.Eexn (xs, None, ML.e_unit)) (ML.I e.e_ity) mask eff attrs
        else let e1 = expr info svar xs.xs_mask e1 in
          let ty = if ity_equal xs.xs_ity ity_unit then None
            else Some (mlty_of_ity xs.xs_mask xs.xs_ity) in
        ML.mk_expr (ML.Eexn (xs, ty, e1)) (ML.I e.e_ity) mask eff attrs

  and ebranch info svar mask ({pp_pat = p; pp_mask = m}, e) =
    (* if the [case] expression is not ghost but there is (at least) one ghost
       branch, then it must be the case that all the branches return [unit]
       and at least one of the non-ghost branches is effectful *)
    if e.e_effect.eff_ghost then (pat m p, ML.e_unit)
    else (pat m p, expr info svar mask e)

  (* type declarations/definitions *)
  let tdef itd =
    let s = itd.itd_its in
    let ddata_constructs = (* point-free *)
      List.map (fun ({rs_cty = cty} as rs) ->
        let args = List.filter pv_not_ghost cty.cty_args in
        (rs.rs_name, List.map (fun {pv_vs = vs} -> type_ vs.vs_ty) args)) in
    let drecord_fields ({rs_cty = cty} as rs) =
      (List.exists (pv_equal (fd_of_rs rs)) s.its_mfields,
      rs.rs_name,
      mlty_of_ity cty.cty_mask cty.cty_result) in
    let id = s.its_ts.ts_name in
    let is_private = s.its_private in
    let args = s.its_ts.ts_args in
    begin match s.its_def, itd.itd_constructors, itd.itd_fields with
      | NoDef, [], [] ->
          ML.mk_its_defn id args is_private None
      | NoDef, cl, [] ->
          let cl = ddata_constructs cl in
          ML.mk_its_defn id args is_private (Some (ML.Ddata cl))
      | NoDef, _, pjl ->
          let p e = not (rs_ghost e) in
          let pjl = filter_ghost_params p drecord_fields pjl in
          begin match pjl with
            | [] ->
                ML.mk_its_defn id args is_private (Some (ML.Dalias ML.tunit))
            | [_, _, ty_pj] when is_optimizable_record_itd itd ->
                ML.mk_its_defn id args is_private (Some (ML.Dalias ty_pj))
            | pjl ->
                ML.mk_its_defn id args is_private (Some (ML.Drecord pjl)) end
      | Alias t, _, _ ->
          ML.mk_its_defn id args is_private (* FIXME ? is this a good mask ? *)
            (Some (ML.Dalias (mlty_of_ity MaskVisible t)))
      | Range r, [], [] ->
          assert (args = []); (* a range type is not polymorphic *)
          ML.mk_its_defn id [] is_private (Some (ML.Drange r))
      | Float ff, [], [] ->
          assert (args = []); (* a float type is not polymorphic *)
          ML.mk_its_defn id [] is_private (Some (ML.Dfloat ff))
      | (Range _ | Float _), _, _ ->
          assert false (* cannot have constructors or fields *)
    end

  let is_val = function
    | Eexec ({c_node = Cany}, _) -> true
    | _ -> false

  let pdecl info pd =
    match pd.pd_node with
    | PDlet (LDvar (_, e)) when e_ghost e ->
        []
    | PDlet (LDvar (pv, e)) when pv.pv_ghost ->
        Debug.dprintf debug_compile "compiling top-level ghost symbol %a@."
          print_pv pv;
        if eff_pure e.e_effect then []
        else let unit_ = pv (* create_pvsymbol (id_fresh "_") ity_unit *) in
          [ML.Dlet (ML.Lvar (unit_, expr info Stv.empty MaskGhost e))]
    | PDlet (LDvar (pv, {e_node = Eexec ({c_node = Cany}, cty)})) ->
        Debug.dprintf debug_compile "compiling undefined constant %a@"
          print_pv pv;
        let ty = mlty_of_ity cty.cty_mask cty.cty_result in
        [ML.Dval (pv, ty)]
    | PDlet (LDvar (pv, e)) ->
        Debug.dprintf debug_compile "compiling top-level symbol %a@."
          print_pv pv;
        [ML.Dlet (ML.Lvar (pv, expr info Stv.empty e.e_mask e))]
    | PDlet (LDsym (rs, _)) when rs_ghost rs ->
        []
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cany})) ->
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        [ML.Dlet (ML.Lany (rs, res, args))]
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e}))
      when is_val e.e_node -> (* zero argument functions *)
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        [ML.Dlet (ML.Lany (rs, res, []))]
    | PDlet (LDsym ({rs_cty = cty; rs_logic} as rs, {c_node = Cfun e; c_cty}))
      when c_cty.cty_args = [] ->
        Debug.dprintf debug_compile "compiling zero-arguments function %a@."
          Expr.print_rs rs;
        Debug.dprintf debug_compile "rs_cty_eff:%b@. c_cty_eff:%b@."
          (cty_pure cty) (cty_pure c_cty);
        Debug.dprintf debug_compile "e_eff:%b@." (eff_pure e.e_effect);
        let args = match rs_logic with RLnone ->
          Debug.dprintf debug_compile "rlnone ici@."; [ML.mk_var_unit]
                                     | _ -> [] in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let svar =
          let args' = List.map (fun (_, ty, _) -> ty) args in
          let svar  = List.fold_left add_tvar Stv.empty args' in
          add_tvar svar res in
        let e = expr info svar cty.cty_mask e in
        [ML.Dlet (ML.Lsym (rs, res, args, e))]
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e})) ->
        Debug.dprintf debug_compile "compiling function %a@." Expr.print_rs rs;
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let svar =
          let args' = List.map (fun (_, ty, _) -> ty) args in
          let svar  = List.fold_left add_tvar Stv.empty args' in
          add_tvar svar res in
        let e = expr info svar cty.cty_mask e in
        [ML.Dlet (ML.Lsym (rs, res, args, e))]
    | PDlet (LDrec rl) ->
        let rl = filter_out_ghost_rdef rl in
        List.iter (fun {rec_sym = rs1; rec_rsym = rs2} ->
            Hrs.replace ht_rs rs2 rs1) rl;
        let def {rec_fun = e; rec_sym = rs1} =
          let e = match e.c_node with Cfun e -> e | _ -> assert false in
          let args = params rs1.rs_cty.cty_args in
          let res  = mlty_of_ity rs1.rs_cty.cty_mask rs1.rs_cty.cty_result in
          let svar =
            let args' = List.map (fun (_, ty, _) -> ty) args in
            let svar  = List.fold_left add_tvar Stv.empty args' in
            add_tvar svar res in
          let e = expr info svar rs1.rs_cty.cty_mask e in
          { ML.rec_sym  = rs1; ML.rec_args = args; ML.rec_exp  = e;
            ML.rec_res  = res; ML.rec_svar = svar; } in
        if rl = [] then [] else [ML.Dlet (ML.Lrec (List.map def rl))]
    | PDlet (LDsym _) | PDpure ->
        []
    | PDtype itl ->
        let itsd = List.map tdef itl in
        [ML.Dtype itsd]
    | PDexn xs ->
        if ity_equal xs.xs_ity ity_unit || xs.xs_mask = MaskGhost then
          [ML.Dexn (xs, None)]
        else [ML.Dexn (xs, Some (mlty_of_ity xs.xs_mask xs.xs_ity))]

  let pdecl_m m pd =
    let info = { ML.from_mod = Some m; ML.from_km = m.mod_known; } in
    pdecl info pd

  (* unit module declarations *)
  let rec mdecl info = function
    | Udecl pd -> pdecl info pd
    | Uscope (_, ([Uuse _] | [Uclone _])) -> []
    | Uscope (s, dl) -> let dl = List.concat (List.map (mdecl info) dl) in
        [ML.Dmodule (s, dl)]
    | Uuse _ | Uclone _ | Umeta _ -> []

  (* modules *)
  let module_ m =
    let from = { ML.from_mod = Some m; ML.from_km = m.mod_known; } in
    let mod_decl = List.concat (List.map (mdecl from) m.mod_units) in
    let add_decl known_map decl = let idl = ML.get_decl_name decl in
      List.fold_left (ML.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add_decl Mid.empty mod_decl in {
      ML.mod_from = from;
      ML.mod_decl = mod_decl;
      ML.mod_known = mod_known;
    }

end

(** Some transformations *)

module Transform = struct

  open Mltree

  let no_reads_writes_conflict spv spv_mreg =
    (* let is_not_write {pv_ity = ity} = match ity.ity_node with
     *   | Ityreg rho -> not (Mreg.mem rho spv_mreg)
     *   | _ -> true in
     * Spv.for_all is_not_write spv *)
    Spv.is_empty (pvs_affected spv_mreg spv)

  let rec can_inline ({e_effect = eff1} as e1) ({e_effect = eff2} as e2) =
    match e2.e_node with
    | Evar _ | Econst _ | Eapp _ | Eassign [_] -> true
    | Elet (Lvar (_, {e_effect = eff1'}), e2') ->
       no_reads_writes_conflict eff1.eff_reads eff1'.eff_writes
       && can_inline e1 e2'
    | _ -> no_reads_writes_conflict eff1.eff_reads eff2.eff_writes

  let mk_list_eb ebl f =
    let mk_acc e (e_acc, s_acc) =
      let e, s = f e in e::e_acc, Spv.union s s_acc in
    List.fold_right mk_acc ebl ([], Spv.empty)

  let rec expr info subst e =
    let mk e_node = { e with e_node = e_node } in
    let add_subst pv e1 e2 = expr info (Mpv.add pv e1 subst) e2 in
    match e.e_node with
    | Evar pv -> begin try Mpv.find pv subst, Spv.singleton pv
        with Not_found -> e, Spv.empty end
    | Elet (Lvar (pv, ({e_effect = eff1} as e1)), e2)
      when Sattr.mem proxy_attr pv.pv_vs.vs_name.id_attrs &&
           eff_pure eff1 &&
           can_inline e1 e2 ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = add_subst pv e1 e2 in
        let s_union = Spv.union s1 s2 in
        if Spv.mem pv s2 then e2, s_union (* [pv] was substituted in [e2] *)
        else (* [pv] was not substituted in [e2], e.g [e2] is an [Efun] *)
          mk (Elet (Lvar (pv, e1), e2)), s_union
    | Elet (ld, e) ->
        let e, spv = expr info subst e in
        let e_let, spv_let = let_def info subst ld in
        mk (Elet (e_let, e)), Spv.union spv spv_let
    | Eapp (rs, el) ->
        let e_app, spv = mk_list_eb el (expr info subst) in
        mk (Eapp (rs, e_app)), spv
    | Efun (vl, e) ->
        (* For now, we accept to inline constants and constructors
           with zero arguments inside a [Efun]. *)
        let p _k e = match e.e_node with
          | Econst _ -> true
          | Eapp (rs, []) when Translate.isconstructor info rs -> true
          | _ -> false in
        let restrict_subst = Mpv.filter p subst in
        (* We begin the inlining of proxy variables in an [Efun] with a
           restricted substitution. This keeps some proxy lets, preventing
           undiserable captures inside the [Efun] expression. *)
        let e, spv = expr info restrict_subst e in
        mk (Efun (vl, e)), spv
    | Eif (e1, e2, e3) ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = expr info subst e2 in
        let e3, s3 = expr info subst e3 in
        mk (Eif (e1, e2, e3)), Spv.union (Spv.union s1 s2) s3
    | Eexn (xs, ty, e1) ->
        let e1, s1 = expr info subst e1 in
        mk (Eexn (xs, ty, e1)), s1
    | Ematch (e, bl, xl) ->
        let e, spv = expr info subst e in
        let e_bl, spv_bl = mk_list_eb bl (branch info subst) in
        let e_xl, spv_xl = mk_list_eb xl (xbranch info subst) in
        mk (Ematch (e, e_bl, e_xl)), Spv.union (Spv.union spv spv_bl) spv_xl
(*
    | Etry (e, case, bl) ->
        let e, spv = expr info subst e in
        let e_bl, spv_bl = mk_list_eb bl (xbranch info subst) in
        mk (Etry (e, case, e_bl)), Spv.union spv spv_bl
*)
    | Eblock el ->
        let e_app, spv = mk_list_eb el (expr info subst) in
        mk (Eblock e_app), spv
    | Ewhile (e1, e2) ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = expr info subst e2 in
        mk (Ewhile (e1, e2)), Spv.union s1 s2
    | Efor (x, pv1, dir, pv2, e) ->
        let e, spv = expr info subst e in
        mk (Efor (x, pv1, dir, pv2, e)), spv
    | Eraise (exn, None) -> mk (Eraise (exn, None)), Spv.empty
    | Eraise (exn, Some e) ->
        let e, spv = expr info subst e in
        mk (Eraise (exn, Some e)), spv
    | Eassign al ->
       let al, s =
         List.fold_left
           (fun (accl, spv) (pv,rs,e) ->
             let e, s = expr info subst e in
             ((pv, rs, e)::accl, Spv.union spv s))
           ([], Spv.empty) al in
       mk (Eassign (List.rev al)), s
    | Econst _ | Eabsurd -> e, Spv.empty
    | Eignore e ->
        let e, spv = expr info subst e in
        mk (Eignore e), spv

  and branch info subst (pat, e) =
    let e, spv = expr info subst e in (pat, e), spv
  and xbranch info subst (exn, pvl, e) =
    let e, spv = expr info subst e in (exn, pvl, e), spv

  and let_def info subst = function
    | Lvar (pv, e) ->
        assert (not (Mpv.mem pv subst)); (* no capture *)
        let e, spv = expr info subst e in
        Lvar (pv, e), spv
    | Lsym (rs, res, args, e) ->
        let e, spv = expr info subst e in
        Lsym (rs, res, args, e), spv
    | Lany _ as lany -> lany, Mpv.empty
    | Lrec rl ->
        let rdef, spv = mk_list_eb rl (rdef info subst) in
        Lrec rdef, spv

  and rdef info subst r =
    let rec_exp, spv = expr info subst r.rec_exp in
    { r with rec_exp = rec_exp }, spv

  let rec pdecl info = function
    | Dtype _ | Dexn _ | Dval _ as d -> d
    | Dmodule (id, dl) ->
        let dl = List.map (pdecl info) dl in Dmodule (id, dl)
    | Dlet def ->
        (* for top-level symbols we can forget the set of inlined variables *)
        let e, _ = let_def info Mpv.empty def in Dlet e

  let module_ m =
    let mod_decl = List.map (pdecl m.mod_from) m.mod_decl in
    let add known_map decl =
      let idl = Mltree.get_decl_name decl in
      List.fold_left (Mltree.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add Mid.empty mod_decl in
    { m with mod_decl = mod_decl; mod_known = mod_known }

end
