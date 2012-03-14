(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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
open Mlw_expr

type ps_ls = { ps : psymbol; ls : lsymbol }

type pconstructor = ps_ls * ps_ls option list

type ity_defn =
  | ITabstract
  | ITalgebraic of pconstructor list

type ity_decl = itysymbol * ity_defn

type pdecl = {
  pd_node : pdecl_node;
  pd_syms : Sid.t;         (* idents used in declaration *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node =
  | PDtype of ity_decl list

let pd_equal : pdecl -> pdecl -> bool = (==)

let mk_decl =
  let r = ref 0 in
  fun node syms news ->
    incr r;
    { pd_node = node; pd_syms = syms; pd_news = news; pd_tag = !r; }

let news_id s id = Sid.add_new (Decl.ClashIdent id) id s

let syms_ts s ts = Sid.add ts.ts_name s
let syms_ls s ls = Sid.add ls.ls_name s

let syms_its s its = Sid.add its.its_pure.ts_name s
let syms_ps s ps = Sid.add ps.p_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ty syms_ls s t

let syms_ity s ity = ity_s_fold syms_its syms_ts s ity

(** {2 Declaration constructors} *)

type pre_pconstructor = preid * (pvsymbol * bool) list

type pre_ity_defn =
  | PITabstract
  | PITalgebraic of pre_pconstructor list

type pre_ity_decl = itysymbol * pre_ity_defn

exception ConstantConstructor of ident

let create_ity_decl tdl =
  let syms = ref Sid.empty in
  let add s (its,_) = news_id s its.its_pure.ts_name in
  let news = ref (List.fold_left add Sid.empty tdl) in
  let projections = Hvs.create 17 in (* vs -> ps_ls *)
  let build_constructor its (id, al) =
    if al = [] then raise (ConstantConstructor (id_register id));
    (* check well-formedness *)
    let tvs = List.fold_right Stv.add its.its_args Stv.empty in
    let regs = List.fold_right Sreg.add its.its_regs Sreg.empty in
    let check_tv tv =
      if not (Stv.mem tv tvs) then raise (UnboundTypeVar tv); true in
    let check_reg r =
      if not (Sreg.mem r regs) then raise (UnboundRegion r); true in
    let check_pv (pv,_) = match pv.pv_mutable with
      | None -> ignore (ity_v_all check_tv check_reg pv.pv_ity)
      | Some r -> if not (Sreg.mem r regs) then raise (UnboundRegion r)
    in
    List.iter check_pv al;
    (* build the constructor ps *)
    let ity = ity_app its (List.map ity_var its.its_args) its.its_regs in
    let result = create_pvsymbol (id_fresh "result") ity in
    let ty_args = List.map (fun (pv, _) -> pv.pv_vs.vs_ty) al in
    let ls = create_fsymbol id ty_args (ty_of_ity ity) in
    let tl = List.map (fun (pv,_) -> t_var pv.pv_vs) al in
    let post = t_equ (t_var result.pv_vs) (t_app ls tl ls.ls_value) in
    let add_erase ef (pv,_) = option_fold eff_reset ef pv.pv_mutable in
    let effect = List.fold_left add_erase eff_empty al in
    let al, (a, _) = Util.chop_last al in
    let c = vty_arrow a ~post ~effect (vty_value result) in
    let arrow (pv,_) c = vty_arrow pv c in
    let v = List.fold_right arrow al c in
    let ps = create_psymbol id Stv.empty Sreg.empty v in
    let ps_ls = { ps = ps; ls = ls } in
    news := Sid.add ps.p_name !news;
    (* build the projections, if any *)
    let build_proj pv =
      let id = id_clone pv.pv_vs.vs_name in
      let ls = create_fsymbol id [result.pv_vs.vs_ty] pv.pv_vs.vs_ty in
      let t = fs_app ls [t_var result.pv_vs] pv.pv_vs.vs_ty in
      let post = t_equ (t_var pv.pv_vs) t in
      let effect = option_fold eff_read eff_empty pv.pv_mutable in
      let vty = vty_arrow result ~post ~effect (vty_value pv) in
      let ps = create_psymbol id Stv.empty Sreg.empty vty in
      let ps_ls = { ps = ps; ls = ls } in
      news := Sid.add ps.p_name !news;
      Hvs.add projections pv.pv_vs ps_ls;
      ps_ls
    in
    let build_proj pv =
      try Hvs.find projections pv.pv_vs with Not_found -> build_proj pv in
    let build_proj (pv, pj) =
      syms := ity_s_fold syms_its syms_ts !syms pv.pv_ity;
      if pj then Some (build_proj pv) else None in
    ps_ls, List.map build_proj al
  in
  let build_type (its, defn) = its, match defn with
    | PITabstract -> ITabstract
    | PITalgebraic cl ->
        Hvs.clear projections;
        ITalgebraic (List.map (build_constructor its) cl)
  in
  let tdl = List.map build_type tdl in
  mk_decl (PDtype tdl) !syms !news


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

let known_add_decl lkn0 kn0 decl =
  let kn = Mid.map (const decl) decl.pd_news in
  let check id decl0 _ =
    if pd_equal decl0 decl
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id)
  in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff decl.pd_syms kn in
  let unk = Mid.set_diff unk lkn0 in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk))
