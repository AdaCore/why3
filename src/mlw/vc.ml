(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Ity
open Expr
open Pdecl

let rec reg_affected wr reg = Mreg.mem reg wr ||
                              Util.any reg_exp_fold (reg_affected wr) reg
let     ity_affected wr ity = Util.any ity_exp_fold (reg_affected wr) ity

let rec reg_aff_regs wr s reg =
  let q = reg_exp_fold (reg_aff_regs wr) Sreg.empty reg in
  let s = Sreg.union s q in
  if not (Sreg.is_empty q) || Mreg.mem reg wr then Sreg.add reg s else s

let ity_aff_regs wr s ity = ity_exp_fold (reg_aff_regs wr) s ity

let ls_of_rs s = match s.rs_logic with RLls ls -> ls | _ -> assert false

let rec explore_paths kn aff mreg t ity =
  if ity.ity_imm then mreg else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r when not (Sreg.mem r aff) -> mreg
  | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
      let rec height t = match t.t_node with
        | Tvar _ -> 0 | Tapp (_,[t]) -> height t + 1
        | _ -> assert false (* shouldn't happen *) in
      let min t o = if height t < height o then t else o in
      let mreg = Mreg.change (fun o -> Some (Opt.fold min t o)) r mreg in
      explore_its kn aff mreg t s tl rl
  | Ityapp (s,tl,rl) -> explore_its kn aff mreg t s tl rl

and explore_its kn aff mreg t s tl rl =
  let isb = its_match_regs s tl rl in
  let follow mreg rs =
    let ity = ity_full_inst isb rs.rs_cty.cty_result in
    let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
    explore_paths kn aff mreg (t_app ls [t] ty) ity in
  List.fold_left follow mreg (find_its_defn kn s).itd_fields

let name_regions kn wr mvs =
  let collect v _ aff = ity_aff_regs wr aff (restore_pv v).pv_ity in
  let aff = Mvs.fold collect mvs Sreg.empty in
  let fill v t mreg = explore_paths kn aff mreg t (restore_pv v).pv_ity in
  let mreg = Mvs.fold fill mvs Mreg.empty in
  let complete r nm _ = if nm <> None then nm else
    let ty = ty_app r.reg_its.its_ts (List.map ty_of_ity r.reg_args) in
    Some (t_var (create_vsymbol (id_clone r.reg_name) ty)) in
  Mreg.merge complete mreg aff

let rec havoc kn wr mreg t ity =
  if not (ity_affected wr ity) then t, [] else
  let split l = let tl, fll = List.split l in tl, List.concat fll in
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg ({reg_its = s} as r) when s.its_nonfree || Mreg.mem r wr ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s r.reg_args r.reg_regs in
      let wfs = Mreg.find_def Mpv.empty r wr in
      let nt = Mreg.find r mreg in
      let field rs =
        if Mpv.mem (Opt.get rs.rs_field) wfs then [] else
        let ity = ity_full_inst isb rs.rs_cty.cty_result in
        let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
        let t = t_app ls [t] ty and nt = t_app ls [nt] ty in
        let t, fl = havoc kn wr mreg t ity in
        if t_equal nt t then fl else t_equ nt t :: fl in
      nt, List.concat (List.map field itd.itd_fields)
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s tl rl in
      begin match itd.itd_constructors with
      | [{rs_logic = RLls cs}] (* record *)
        when List.length cs.ls_args = List.length itd.itd_fields ->
          let field rs =
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            havoc kn wr mreg (t_app_infer (ls_of_rs rs) [t]) ity in
          let tl, fl = split (List.map field itd.itd_fields) in
          fs_app cs tl (ty_of_ity ity), fl
      | cl ->
          let ty = ty_of_ity ity in
          let branch ({rs_cty = cty} as rs) =
            let cs = ls_of_rs rs in
            let get_ity v = ity_full_inst isb v.pv_ity in
            let ityl = List.map get_ity cty.cty_args in
            let get_pjv {pv_vs = {vs_name = id}} ity =
              create_vsymbol (id_clone id) (ty_of_ity ity) in
            let vl = List.map2 get_pjv cty.cty_args ityl in
            let p = pat_app cs (List.map pat_var vl) ty in
            let get_hv v ity = havoc kn wr mreg (t_var v) ity in
            let tl, fl = split (List.map2 get_hv vl ityl) in
            (p, fs_app cs tl ty), (p, t_and_simp_l fl) in
          let tbl, fbl = List.split (List.map branch cl) in
          let f = t_case_close_simp t fbl in
          let f = if t_equal f t_true then [] else [f] in
          t_case_close t tbl, f
      end

let havoc_fast kn {eff_writes = wr; eff_covers = cv} mvs =
  if Sreg.is_empty cv then [] else
  let mreg = name_regions kn cv mvs in
  let update v nt acc =
    let t, fl = havoc kn wr mreg (t_var v) (restore_pv v).pv_ity in
    (if t_equal nt t then fl else t_equ nt t :: fl) @ acc in
  Mvs.fold update mvs []

let clone_vs {vs_name = id; vs_ty = ty} =
  t_var (create_vsymbol (id_clone id) ty)

let _step_back wr1 rd2 wr2 mvs =
  if Mreg.is_empty wr1 then Mvs.empty else
  let back v t =
    let ity = (restore_pv v).pv_ity in
    if not (ity_affected wr1 ity) then None else
    if not (ity_affected wr2 ity) then Some t else
    Some (clone_vs v) in
  let mvs = Mvs.mapi_filter back mvs in
  let add {pv_vs = v; pv_ity = ity} acc =
    if Mvs.mem v mvs || not (ity_affected wr1 ity)
    then acc else Mvs.add v (clone_vs v) acc in
  Spv.fold add rd2 mvs

let vc _env kn d = match d.pd_node with
  | PDlet (LDsym (s,{c_cty = {cty_effect = eff}})) ->
      let add_read v mvs =
        let nm = v.pv_vs.vs_name.id_string ^ "_new" in
        let id = id_derive nm v.pv_vs.vs_name in
        let nv = create_vsymbol id v.pv_vs.vs_ty in
        Mvs.add v.pv_vs (t_var nv) mvs in
      let mvs = Spv.fold add_read eff.eff_reads Mvs.empty in
      let f = t_and_simp_l (havoc_fast kn eff mvs) in
      let fvs = Mvs.domain (t_freevars Mvs.empty f) in
      let f = t_forall_close (Svs.elements fvs) [] f in
      let pr = create_prsymbol (id_fresh (s.rs_name.id_string ^ "_havoc")) in
      [create_pure_decl (create_prop_decl Pgoal pr f)]
  | _ -> []

