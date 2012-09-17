(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why3
open Util
open Ident
open Ty
open Term
open Decl
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

type constructor = plsymbol * plsymbol option list

type data_decl = itysymbol * constructor list * post

type pdecl = {
  pd_node : pdecl_node;
(*   pd_syms : Sid.t;         (* idents used in declaration *) *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node =
  | PDtype of itysymbol
  | PDdata of data_decl list
  | PDval  of let_sym
  | PDlet  of let_defn
  | PDrec  of rec_defn
  | PDexn  of xsymbol

let pd_equal : pdecl -> pdecl -> bool = (==)

let mk_decl =
  let r = ref 0 in
  fun node (*syms*) news ->
    incr r;
    { pd_node = node; (*pd_syms = syms;*) pd_news = news; pd_tag = !r; }

let news_id s id = Sid.add_new (Decl.ClashIdent id) id s

(*
let syms_ts s ts = Sid.add ts.ts_name s
let syms_ls s ls = Sid.add ls.ls_name s

let syms_ps s ps = Sid.add ps.ps_name s
let syms_xs s xs = Sid.add xs.xs_name s
let syms_pl s pl = Sid.add pl.pl_ls.ls_name s

let syms_its s its = Sid.add its.its_pure.ts_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ty syms_ls s t

let syms_ity s ity = ity_s_fold syms_its syms_ts s ity

let syms_effect s eff =
  let add_raise xs s = syms_ity (syms_xs s xs) xs.xs_ity in
  let s = Sexn.fold add_raise eff.eff_raises s in
  let s = Sexn.fold add_raise eff.eff_ghostx s in
  s

let syms_post s q = syms_term s (term_of_post q)

let syms_xpost s xq =
  let add_xq xs q s = syms_post (syms_xs s xs) q in
  Mexn.fold add_xq xq s

let syms_varmap s m = Sid.union s (Mid.map (fun _ -> ()) m)

let rec syms_type_c s tyc =
  let s = syms_term s tyc.c_pre in
  let s = syms_post s tyc.c_post in
  let s = syms_xpost s tyc.c_xpost in
  let s = syms_effect s tyc.c_effect in
  syms_type_v s tyc.c_result

and syms_type_v s = function
  | SpecV vtv -> syms_ity s vtv.vtv_ity
  | SpecA (pvl,tyc) ->
      let add_pv s pv = syms_ity s pv.pv_vtv.vtv_ity in
      List.fold_left add_pv (syms_type_c s tyc) pvl

let rec syms_vta s a =
  let s = syms_ity s a.vta_arg.vtv_ity in
  let s = syms_effect s a.vta_effect in
  syms_vty s a.vta_result

and syms_vty s = function
  | VTvalue vtv -> syms_ity s vtv.vtv_ity
  | VTarrow vta -> syms_vta s vta

let syms_expr s _e = s (* TODO *)
*)

(** {2 Declaration constructors} *)

let create_ty_decl its =
(*   let syms = Util.option_fold syms_ity Sid.empty its.its_def in *)
  let news = Sid.singleton its.its_pure.ts_name in
  mk_decl (PDtype its) (*syms*) news

type pre_constructor = preid * (pvsymbol * bool) list

type pre_data_decl = itysymbol * pre_constructor list

let null_invariant { its_pure = ts } =
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let vs = create_vsymbol (id_fresh "dummy") ty in
  create_post vs t_true

let create_data_decl tdl =
(*   let syms = ref Sid.empty in *)
  let news = ref Sid.empty in
  let projections = Hid.create 17 in (* id -> plsymbol *)
  let build_constructor its (id,al) =
    (* check well-formedness *)
    let vtvs = List.map (fun (pv,_) -> pv.pv_vtv) al in
    let tvs = List.fold_right Stv.add its.its_args Stv.empty in
    let regs = List.fold_right Sreg.add its.its_regs Sreg.empty in
    let check_vars { vars_tv = atvs; vars_reg = aregs } =
      if not (Stv.subset atvs tvs) then
        raise (UnboundTypeVar (Stv.choose (Stv.diff atvs tvs)));
      if not (Sreg.subset aregs regs) then
        raise (UnboundRegion (Sreg.choose (Sreg.diff aregs regs))) in
    let check_arg vtv = match vtv.vtv_mut with
      | Some r -> if not (Sreg.mem r regs) then raise (UnboundRegion r)
      | None -> check_vars vtv.vtv_ity.ity_vars in
    List.iter check_arg vtvs;
    (* build the constructor ps *)
    let hidden = its.its_abst in
    let rdonly = its.its_priv in
    let tvl = List.map ity_var its.its_args in
    let res = vty_value (ity_app its tvl its.its_regs) in
    let pls = create_plsymbol ~hidden ~rdonly id vtvs res in
    news := news_id !news pls.pl_ls.ls_name;
    (* build the projections, if any *)
    let build_proj id vtv =
      try Hid.find projections id with Not_found ->
      let pls = create_plsymbol ~hidden (id_clone id) [res] vtv in
      news := news_id !news pls.pl_ls.ls_name;
      Hid.add projections id pls;
      pls
    in
    let build_proj (pv,pj) =
      let vtv = pv.pv_vtv in
(*       syms := ity_s_fold syms_its syms_ts !syms vtv.vtv_ity; *)
      if pj then Some (build_proj pv.pv_vs.vs_name vtv) else None
    in
    pls, List.map build_proj al
  in
  let build_type (its,cl) =
    Hid.clear projections;
    news := news_id !news its.its_pure.ts_name;
    its, List.map (build_constructor its) cl, null_invariant its
  in
  let tdl = List.map build_type tdl in
  mk_decl (PDdata tdl) (*!syms*) !news

let add_invariant pd its p =
  if not its.its_inv then invalid_arg "Mlw_decl.add_invariant";
  Mvs.iter (fun vs _ -> raise (Decl.UnboundVar vs)) p.t_vars;
  let rec add = function
    | (s, cls, inv) :: tdl when its_equal s its ->
        check_post (t_type inv) p;
        let v, q = open_post inv in
        let u, p = open_post p in
        let q = t_and_simp (t_subst_single v (t_var u) q) p in
        let inv = create_post u q in
        (s, cls, inv) :: tdl
    | td :: tdl ->
        td :: add tdl
    | [] -> raise Not_found
  in
  match pd.pd_node with
    | PDdata tdl -> mk_decl (PDdata (add tdl)) (*pd.pd_syms*) pd.pd_news
    | _ -> invalid_arg "Mlw_decl.add_invariant"

let check_vars vars =
  if not (Stv.is_empty vars.vars_tv) then
    raise (UnboundTypeVar (Stv.choose vars.vars_tv))

let letvar_news = function
  | LetV pv -> check_vars pv.pv_vars; Sid.singleton pv.pv_vs.vs_name
  | LetA ps -> check_vars ps.ps_vars; Sid.singleton ps.ps_name

let new_regs old_vars news vars =
  let on_reg r acc = Sreg.union r.reg_ity.ity_vars.vars_reg acc in
  let old_regs = reg_fold on_reg old_vars old_vars.vars_reg in
  let regs = reg_fold on_reg vars vars.vars_reg in
  let regs = Sreg.diff regs old_regs in
  Sreg.fold (fun r s -> news_id s r.reg_name) regs news

let create_let_decl ld =
  let vars = vars_merge ld.let_expr.e_varm vars_empty in
  let news = letvar_news ld.let_sym in
  let news = match ld.let_sym with
    | LetA ps -> new_regs vars news ps.ps_vars
    | LetV pv -> new_regs vars news pv.pv_vars in
(*
  let syms = syms_varmap Sid.empty ld.let_expr.e_vars in
  let syms = syms_effect syms ld.let_expr.e_effect in
  let syms = syms_vty syms ld.let_expr.e_vty in
  let syms = syms_expr syms ld.let_expr in
*)
  mk_decl (PDlet ld) (*syms*) news

let create_rec_decl ({ rec_defn = rdl } as d) =
  let add_rd s { fun_ps = p } =
    check_vars p.ps_vars; news_id s p.ps_name in
  let news = List.fold_left add_rd Sid.empty rdl in
(*
  let add_rd syms { rec_ps = ps; rec_lambda = l; rec_vars = vm } =
    let syms = syms_varmap syms vm in
    let syms = syms_vta syms ps.ps_vta in
    let syms = syms_term syms l.l_pre in
    let syms = syms_post syms l.l_post in
    let syms = syms_xpost syms l.l_xpost in
    let addv s { v_term = t; v_rel = ls } =
      Util.option_fold syms_ls (syms_term s t) ls in
    let syms = List.fold_left addv syms l.l_variant in
    syms_expr syms l.l_expr in
  let syms = List.fold_left add_rd Sid.empty rdl in
*)
  mk_decl (PDrec d) (*syms*) news

let create_val_decl lv =
  let news = letvar_news lv in
  let news = match lv with
    | LetV { pv_vtv = { vtv_mut = Some _ }} ->
        Loc.errorm "abstract parameters cannot be mutable"
    | LetV pv -> new_regs vars_empty news pv.pv_vars
    | LetA _ -> news in
(*
  let syms = syms_type_v Sid.empty vd.val_spec in
  let syms = syms_varmap syms vd.val_vars in
*)
  mk_decl (PDval lv) (*syms*) news

let create_exn_decl xs =
  let news = Sid.singleton xs.xs_name in
(*
  let syms = syms_ity Sid.empty xs.xs_ity in
*)
  mk_decl (PDexn xs) (*syms*) news

(** {2 Cloning} *)

let clone_data_decl sm pd = match pd.pd_node with
  | PDdata tdl ->
      let news = ref Sid.empty in
      let add_pl pl =
        let pl = Mls.find pl.pl_ls sm.sm_pls in
        news := news_id !news pl.pl_ls.ls_name;
        pl in
      let add_cs (cs,pjl) =
        add_pl cs, List.map (Util.option_map add_pl) pjl in
      let add_td (its,csl,inv) =
        let conv_ts ts = Mts.find_def ts ts sm.sm_pure.Theory.sm_ts in
        let conv_ls ls = Mls.find_def ls ls sm.sm_pure.Theory.sm_ls in
        let inv = Term.t_s_map (Ty.ty_s_map conv_ts) conv_ls inv in
        let its = Mits.find its sm.sm_its in
        news := news_id !news its.its_pure.ts_name;
        its, List.map add_cs csl, inv in
      let tdl = List.map add_td tdl in
      mk_decl (PDdata tdl) (*!syms*) !news
  | _ -> invalid_arg "Mlw_decl.clone_data_decl"

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if pd_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id)
  in
  Mid.union check_known kn1 kn2

let pd_vars pd = match pd.pd_node with
  | PDval (LetV _) -> Sid.empty
  | PDval (LetA ps) -> Mid.map (fun _ -> ()) ps.ps_varm
  | PDlet ld -> Mid.map (fun _ -> ()) ld.let_expr.e_varm
  | PDrec rd ->
      let add_rd s fd = Mid.set_union s fd.fun_ps.ps_varm in
      let varm = List.fold_left add_rd Mid.empty rd.rec_defn in
      Mid.map (fun _ -> ()) varm
  | PDtype _ | PDdata _ | PDexn _ -> Sid.empty

let known_add_decl lkn0 kn0 d =
  let kn = Mid.map (const d) d.pd_news in
  let check id decl0 _ =
    if pd_equal decl0 d
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id) in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff (pd_vars d) kn in
  let unk = Mid.set_diff unk lkn0 in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk))

let rec find_td its1 = function
  | (its2,csl,inv) :: _ when its_equal its1 its2 -> csl,inv
  | _ :: tdl -> find_td its1 tdl
  | [] -> raise Not_found

let find_constructors kn its =
  match (Mid.find its.its_pure.ts_name kn).pd_node with
  | PDtype _ -> []
  | PDdata tdl -> fst (find_td its tdl)
  | PDval _ | PDlet _ | PDrec _ | PDexn _ -> assert false

let find_invariant kn its =
  match (Mid.find its.its_pure.ts_name kn).pd_node with
  | PDtype _ -> null_invariant its
  | PDdata tdl -> snd (find_td its tdl)
  | PDval _ | PDlet _ | PDrec _ | PDexn _ -> assert false

let check_match lkn _kn d =
  let rec checkE () e = match e.e_node with
    | Ecase (e1,bl) ->
        let typ = ty_of_ity (vtv_of_expr e1).vtv_ity in
        let tye = ty_of_ity (vtv_of_expr e).vtv_ity in
        let t_p = t_var (create_vsymbol (id_fresh "x") typ) in
        let t_e = t_var (create_vsymbol (id_fresh "y") tye) in
        let bl = List.map (fun (pp,_) -> [pp.ppat_pattern], t_e) bl in
        let try3 f = match e.e_loc with Some l -> Loc.try3 l f | None -> f in
        let find ts = List.map fst (Decl.find_constructors lkn ts) in
        ignore (try3 Pattern.CompileTerm.compile find [t_p] bl);
        e_fold checkE () e
    | _ -> e_fold checkE () e
  in
  match d.pd_node with
  | PDrec { rec_defn = fdl } ->
      List.iter (fun fd -> checkE () fd.fun_lambda.l_expr) fdl
  | PDlet { let_expr = e } -> checkE () e
  | PDval _ | PDtype _ | PDdata _ | PDexn _ -> ()

exception NonupdatableType of ity

let inst_constructors lkn kn ity = match ity.ity_node with
  | Itypur (ts,_) ->
      let csl = Decl.find_constructors lkn ts in
      let d = Mid.find ts.ts_name lkn in
      let is_rec = Mid.mem ts.ts_name d.Decl.d_syms in
      if csl = [] || is_rec then raise (NonupdatableType ity);
      let base = ity_pur ts (List.map ity_var ts.ts_args) in
      let sbs = ity_match ity_subst_empty base ity in
      let subst ty = vty_value (ity_full_inst sbs (ity_of_ty ty)) in
      List.map (fun (cs,_) -> cs, List.map subst cs.ls_args) csl
  | Ityapp (its,_,_) ->
      let csl = find_constructors kn its in
      let d = Mid.find its.its_pure.ts_name lkn in
      let is_rec = Mid.mem its.its_pure.ts_name d.Decl.d_syms in
      if csl = [] || is_rec then raise (NonupdatableType ity);
      let base = ity_app its (List.map ity_var its.its_args) its.its_regs in
      let sbs = ity_match ity_subst_empty base ity in
      let subst vtv =
        let ghost = vtv.vtv_ghost in
        let mut = Util.option_map (reg_full_inst sbs) vtv.vtv_mut in
        vty_value ~ghost ?mut (ity_full_inst sbs vtv.vtv_ity) in
      List.map (fun (cs,_) -> cs.pl_ls, List.map subst cs.pl_args) csl
  | Ityvar _ ->
      invalid_arg "Mlw_decl.inst_constructors"

let check_ghost lkn kn d =
  let rec access regs ity =
    let check vtv = match vtv.vtv_mut with
      | _ when vtv.vtv_ghost -> ()
      | Some r when Sreg.mem r regs -> raise (GhostWrite (e_void, r))
      | _ -> access regs vtv.vtv_ity in
    let check (_cs,vtvl) = List.iter check vtvl in
    let occurs r = reg_occurs r ity.ity_vars in
    if not (Sreg.exists occurs regs) then () else
    List.iter check (inst_constructors lkn kn ity)
  in
  let rec check pvs vta =
    let eff = vta.vta_spec.c_effect in
    if not (Sexn.is_empty eff.eff_ghostx) then
      raise (GhostRaise (e_void, Sexn.choose eff.eff_ghostx));
    let pvs = List.fold_right Spv.add vta.vta_args pvs in
    let test pv =
      if pv.pv_vtv.vtv_ghost then () else
      access eff.eff_ghostw pv.pv_vtv.vtv_ity
    in
    Spv.iter test pvs;
    match vta.vta_result with
    | VTarrow vta -> check pvs vta
    | VTvalue _ -> ()
  in
  let check ps =
    if ps.ps_vta.vta_ghost then () else
    check (ps_pvset Spv.empty ps) ps.ps_vta
  in
  match d.pd_node with
  | PDrec rd -> List.iter (fun fd -> check fd.fun_ps) rd.rec_defn
  | PDval (LetA ps) | PDlet { let_sym = LetA ps } -> check ps
  | PDval _ | PDlet _ | PDtype _ | PDdata _ | PDexn _ -> ()

let known_add_decl lkn kn d =
  let kn = known_add_decl lkn kn d in
  check_ghost lkn kn d;
  check_match lkn kn d;
  kn

