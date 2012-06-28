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
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

(*
  module =
    theory +
    namespace +
    program decls (no logic decl here)

  extraction to OCaml
    1. all types
         follow order given by theory, and retrieve program types when necessary
    2. logic decls (no types)
    3. program decls
*)

type type_symbol =
  | PT of itysymbol
  | TS of tysymbol

type prog_symbol =
  | PV of pvsymbol
  | PS of psymbol
  | PL of plsymbol
  | XS of xsymbol
  | LS of lsymbol

type namespace = {
  ns_ts : type_symbol Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ps = Mstr.empty;
  ns_ns = Mstr.empty;
}

let ns_replace sub chk x vo vn =
  if not chk then vn else
  if sub vo vn then vn else
  raise (ClashSymbol x)

let tsym_sub t1 t2 = match t1,t2 with
  | PT t1, PT t2 -> its_equal t1 t2
  | TS t1, TS t2 -> ts_equal t1 t2
  | _, _ -> false

let psym_sub p1 p2 = match p1,p2 with
  | PV p1, PV p2 -> pv_equal p1 p2
  | PS p1, PS p2 -> ps_equal p1 p2
  | PL p1, PL p2 -> pl_equal p1 p2
  | XS p1, XS p2 -> xs_equal p1 p2
  | LS p1, LS p2 -> ls_equal p1 p2
  (* program symbols may overshadow pure symbols *)
  | LS _, (PV _|PS _|PL _|XS _) -> true
  | _, _ -> false

let rec merge_ns chk ns1 ns2 =
  let join sub x n o = Some (ns_replace sub chk x o n) in
  let ns_union sub m1 m2 = Mstr.union (join sub) m1 m2 in
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union tsym_sub ns1.ns_ts ns2.ns_ts;
    ns_ps = ns_union psym_sub ns1.ns_ps ns2.ns_ps;
    ns_ns = Mstr.union fusion ns1.ns_ns ns2.ns_ns; }

let add_ns chk x ns m = Mstr.change (function
  | Some os -> Some (merge_ns chk ns os)
  | None    -> Some ns) x m

let ns_add sub chk x vn m = Mstr.change (function
  | Some vo -> Some (ns_replace sub chk x vo vn)
  | None    -> Some vn) x m

let add_ts chk x ts ns = { ns with ns_ts = ns_add tsym_sub chk x ts ns.ns_ts }
let add_ps chk x pf ns = { ns with ns_ps = ns_add psym_sub chk x pf ns.ns_ps }
let add_ns chk x nn ns = { ns with ns_ns = add_ns          chk x nn ns.ns_ns }

let rec convert_pure_ns ns =
  { ns_ts = Mstr.map (fun ts -> TS ts) ns.Theory.ns_ts;
    ns_ps = Mstr.map (fun ls -> LS ls) ns.Theory.ns_ls;
    ns_ns = Mstr.map convert_pure_ns ns.Theory.ns_ns; }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ps = ns_find (fun ns -> ns.ns_ps)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(** Module *)

type modul = {
  mod_theory: theory;			(* pure theory *)
  mod_decls : pdecl list;		(* module declarations *)
  mod_export: namespace;		(* exported namespace *)
  mod_known : known_map;		(* known identifiers *)
  mod_local : Sid.t;			(* locally declared idents *)
  mod_used  : Sid.t;			(* used modules *)
}

(** Module under construction *)

type module_uc = {
  muc_theory : theory_uc;
  muc_decls  : pdecl list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
}

let empty_module n p = {
  muc_theory = create_theory ~path:p n;
  muc_decls  = [];
  muc_import = [empty_ns];
  muc_export = [empty_ns];
  muc_known  = Mid.empty;
  muc_local  = Sid.empty;
  muc_used   = Sid.empty;
}

let close_module uc =
  let th = close_theory uc.muc_theory in (* catches errors *)
  { mod_theory = th;
    mod_decls  = List.rev uc.muc_decls;
    mod_export = List.hd uc.muc_export;
    mod_known  = uc.muc_known;
    mod_local  = uc.muc_local;
    mod_used   = uc.muc_used; }

let get_theory uc = uc.muc_theory
let get_namespace uc = List.hd uc.muc_import
let get_known uc = uc.muc_known

let open_namespace uc = match uc.muc_import with
  | ns :: _ -> { uc with
      muc_theory = Theory.open_namespace uc.muc_theory;
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_namespace uc import s =
  let th = Theory.close_namespace uc.muc_theory import s in (* catches errors *)
  match uc.muc_import, uc.muc_export with
  | _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
      let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
      { uc with
	  muc_theory = th;
	  muc_import = i1 :: sti;
	  muc_export = e1 :: ste; }
  | _ ->
      assert false

(** Use *)

let add_to_module uc th ns =
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = th;
      muc_import = merge_ns false ns i0 :: sti;
      muc_export = merge_ns true  ns e0 :: ste; }
  | _ -> assert false

let use_export uc m =
  let mth = m.mod_theory in
  let id = mth.th_name in
  let uc =
    if Sid.mem id uc.muc_used then uc else { uc with
      muc_known = merge_known uc.muc_known m.mod_known;
      muc_used  = Sid.add id uc.muc_used } in
  let th = Theory.use_export uc.muc_theory mth in
  add_to_module uc th m.mod_export

(** Logic decls *)

let add_to_theory f uc x = { uc with muc_theory = f uc.muc_theory x }

let add_symbol add id v uc =
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_decl uc d =
  let add_ts uc ts = add_symbol add_ts ts.ts_name (TS ts) uc in
  let add_ls uc ls = add_symbol add_ps ls.ls_name (LS ls) uc in
  let add_pj uc pj = Util.option_fold add_ls uc pj in
  let add_cs uc (cs,pjl) = List.fold_left add_pj (add_ls uc cs) pjl in
  let add_data uc (ts,csl) = List.fold_left add_cs (add_ts uc ts) csl in
  let add_logic uc (ls,_) = add_ls uc ls in
  let uc = match d.Decl.d_node with
    | Decl.Dtype ts -> add_ts uc ts
    | Decl.Ddata dl -> List.fold_left add_data uc dl
    | Decl.Dparam ls -> add_ls uc ls
    | Decl.Dlogic dl -> List.fold_left add_logic uc dl
    | Decl.Dind (_,dl) -> List.fold_left add_logic uc dl
    | Decl.Dprop _ -> uc
  in
  add_to_theory Theory.add_decl uc d

let use_export_theory uc th =
  let nth = Theory.use_export uc.muc_theory th in
  let nns = convert_pure_ns th.th_export in
  add_to_module uc nth nns

let clone_export_theory uc th inst =
  let nth = Theory.clone_export uc.muc_theory th inst in
  let sm = match Theory.get_rev_decls nth with
    | { td_node = Clone (_,sm) } :: _ -> sm
    | _ -> assert false in
  let g_ts _ ts = not (Mts.mem ts inst.inst_ts) in
  let g_ls _ ls = not (Mls.mem ls inst.inst_ls) in
  let f_ts ts = TS (Mts.find_def ts ts sm.sm_ts) in
  let f_ls ls = LS (Mls.find_def ls ls sm.sm_ls) in
  let rec f_ns ns = {
    ns_ts = Mstr.map f_ts (Mstr.filter g_ts ns.Theory.ns_ts);
    ns_ps = Mstr.map f_ls (Mstr.filter g_ls ns.Theory.ns_ls);
    ns_ns = Mstr.map f_ns ns.Theory.ns_ns; }
  in
  add_to_module uc nth (f_ns th.th_export)

let add_meta uc m al =
  { uc with muc_theory = Theory.add_meta uc.muc_theory m al }

(** Program decls *)

let add_type uc its =
  add_symbol add_ts its.its_pure.ts_name (PT its) uc

let add_data uc (its,csl) =
  let add_pl uc pl = add_symbol add_ps pl.pl_ls.ls_name (PL pl) uc in
  let add_pj uc pj = Util.option_fold add_pl uc pj in
  let add_cs uc (cs,pjl) = List.fold_left add_pj (add_pl uc cs) pjl in
  let uc = add_symbol add_ts its.its_pure.ts_name (PT its) uc in
  if its.its_abst then uc else List.fold_left add_cs uc csl

let add_let uc = function
  | LetV pv -> add_symbol add_ps pv.pv_vs.vs_name (PV pv) uc
  | LetA ps -> add_symbol add_ps ps.ps_name (PS ps) uc

let add_rec uc { rec_ps = ps } =
  add_symbol add_ps ps.ps_name (PS ps) uc

let add_exn uc xs =
  add_symbol add_ps xs.xs_name (XS xs) uc

let add_pdecl uc d =
  let uc = { uc with
    muc_decls = d :: uc.muc_decls;
    muc_known = known_add_decl (Theory.get_known uc.muc_theory) uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news }
  in
  match d.pd_node with
  | PDtype its ->
      let uc = add_type uc its in
      add_to_theory Theory.add_ty_decl uc its.its_pure
  | PDdata dl ->
      let uc = List.fold_left add_data uc dl in
      let projection = option_map (fun pls -> pls.pl_ls) in
      let constructor (pls,pjl) = pls.pl_ls, List.map projection pjl in
      let defn cl = List.map constructor cl in
      let dl = List.map (fun (its,cl) -> its.its_pure, defn cl) dl in
      add_to_theory Theory.add_data_decl uc dl
  | PDval { val_name = lv } | PDlet { let_var = lv } ->
      add_let uc lv
  | PDrec rdl ->
      List.fold_left add_rec uc rdl
  | PDexn xs ->
      add_exn uc xs

(* create module *)

let th_unit =
  let ts = create_tysymbol (id_fresh "unit") [] (Some ty_unit) in
  let uc = create_theory (id_fresh "Unit") in
  let uc = Theory.use_export uc (tuple_theory 0) in
  let uc = Theory.add_ty_decl uc ts in
  close_theory uc

let mod_exit =
  let xs = create_xsymbol (id_fresh "%Exit") ity_unit in
  let uc = empty_module (id_fresh "Exit") [] in
  let uc = use_export_theory uc (tuple_theory 0) in
  let uc = add_pdecl uc (create_exn_decl xs) in
  close_module uc

let create_module ?(path=[]) n =
  let m = empty_module n path in
  let m = use_export_theory m bool_theory in
  let m = use_export_theory m th_unit in
  let m = use_export m mod_exit in
  m

(** Clone *)

let clone_export _uc _m _inst =
  assert false (*TODO*)
