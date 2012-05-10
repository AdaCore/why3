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

type data_decl = itysymbol * constructor list

type pdecl = {
  pd_node : pdecl_node;
  pd_syms : Sid.t;         (* idents used in declaration *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node =
  | PDtype of itysymbol
  | PDdata of data_decl list

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
let syms_ps s ps = Sid.add ps.ps_name s

let syms_ty s ty = ty_s_fold syms_ts s ty
let syms_term s t = t_s_fold syms_ty syms_ls s t

let syms_ity s ity = ity_s_fold syms_its syms_ts s ity

(** {2 Declaration constructors} *)

let create_ty_decl its =
  let syms = Util.option_fold syms_ity Sid.empty its.its_def in
  let news = news_id Sid.empty its.its_pure.ts_name in
  mk_decl (PDtype its) syms news

type pre_constructor = preid * (pvsymbol * bool) list

type pre_data_decl = itysymbol * pre_constructor list

let create_data_decl tdl =
  let syms = ref Sid.empty in
  let add s (its,_) = news_id s its.its_pure.ts_name in
  let news = ref (List.fold_left add Sid.empty tdl) in
  let projections = Hid.create 17 in (* id -> plsymbol *)
  let build_constructor its (id,al) =
    (* check well-formedness *)
    let vtvs = List.map (fun (pv,_) -> pv.pv_vtv) al in
    let tvs = List.fold_right Stv.add its.its_args Stv.empty in
    let regs = List.fold_right Sreg.add its.its_regs Sreg.empty in
    let check_tv tv =
      if not (Stv.mem tv tvs) then raise (UnboundTypeVar tv); true in
    let check_reg r =
      if not (Sreg.mem r regs) then raise (UnboundRegion r); true in
    let check_arg vtv = match vtv.vtv_mut with
      | None -> ity_v_all check_tv check_reg vtv.vtv_ity
      | Some r -> check_reg r
    in
    ignore (List.for_all check_arg vtvs);
    (* build the constructor ps *)
    let tvl = List.map ity_var its.its_args in
    let res = vty_value (ity_app its tvl its.its_regs) in
    let pls = create_plsymbol id vtvs res in
    news := Sid.add pls.pl_ls.ls_name !news;
    (* build the projections, if any *)
    let build_proj id vtv =
      try Hid.find projections id with Not_found ->
      let pls = create_plsymbol (id_clone id) [res] vtv in
      news := Sid.add pls.pl_ls.ls_name !news;
      Hid.add projections id pls;
      pls
    in
    let build_proj (pv,pj) =
      let vtv = pv.pv_vtv in
      syms := ity_s_fold syms_its syms_ts !syms vtv.vtv_ity;
      if pj then Some (build_proj pv.pv_vs.vs_name vtv) else None
    in
    pls, List.map build_proj al
  in
  let build_type (its,cl) =
    Hid.clear projections;
    its, List.map (build_constructor its) cl
  in
  let tdl = List.map build_type tdl in
  mk_decl (PDdata tdl) !syms !news


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
