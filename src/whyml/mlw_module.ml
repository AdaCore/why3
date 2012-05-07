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

type prgsymbol =
  | PV of pvsymbol
  | PA of pasymbol
  | PS of psymbol
  | PL of plsymbol

type namespace = {
  ns_it : itysymbol Mstr.t;  (* type symbols *)
  ns_ps : prgsymbol Mstr.t;  (* program symbols *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_it = Mstr.empty;
  ns_ps = Mstr.empty;
  ns_ns = Mstr.empty;
}

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let ns_union eq chk =
  Mstr.union (fun x vn vo -> Some (ns_replace eq chk x vo vn))

let prg_equal p1 p2 = match p1,p2 with
  | PV p1, PV p2 -> pv_equal p1 p2
  | PA p1, PA p2 -> pa_equal p1 p2
  | PS p1, PS p2 -> ps_equal p1 p2
  | PL p1, PL p2 -> pl_equal p1 p2
  | _, _ -> false

let rec merge_ns chk ns1 ns2 =
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_it = ns_union its_equal chk ns1.ns_it ns2.ns_it;
    ns_ps = ns_union prg_equal chk ns1.ns_ps ns2.ns_ps;
    ns_ns = Mstr.union fusion      ns1.ns_ns ns2.ns_ns; }

let nm_add chk x ns m = Mstr.change (function
  | None -> Some ns
  | Some os -> Some (merge_ns chk ns os)) x m

let ns_add eq chk x v m = Mstr.change (function
  | None -> Some v
  | Some vo -> Some (ns_replace eq chk x vo v)) x m

let it_add = ns_add its_equal
let ps_add = ns_add prg_equal

let add_it chk x ts ns = { ns with ns_it = it_add chk x ts ns.ns_it }
let add_ps chk x pf ns = { ns with ns_ps = ps_add chk x pf ns.ns_ps }
let add_ns chk x nn ns = { ns with ns_ns = nm_add chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_it = ns_find (fun ns -> ns.ns_it)
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

let use_export uc m =
  let mth = m.mod_theory in
  let id = mth.th_name in
  let uc =
    if not (Sid.mem id uc.muc_used) then
      { uc with
          muc_known = merge_known uc.muc_known m.mod_known;
          muc_used  = Sid.add id uc.muc_used; }
    else
      uc
  in
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = Theory.use_export uc.muc_theory mth;
      muc_import = merge_ns false m.mod_export i0 :: sti;
      muc_export = merge_ns true  m.mod_export e0 :: ste; }
  | _ -> assert false

(** Logic decls *)

let add_to_theory f uc x = { uc with muc_theory = f uc.muc_theory x }

let add_decl = add_to_theory Theory.add_decl
let add_decl_with_tuples = add_to_theory Theory.add_decl_with_tuples
let add_ty_decl = add_to_theory Theory.add_ty_decl
let add_data_decl = add_to_theory Theory.add_data_decl
let add_param_decl = add_to_theory Theory.add_param_decl
let add_logic_decl = add_to_theory Theory.add_logic_decl
let add_ind_decl = add_to_theory Theory.add_ind_decl
let add_prop_decl uc k pr f =
  { uc with muc_theory = Theory.add_prop_decl uc.muc_theory k pr f }

let use_export_theory = add_to_theory Theory.use_export
let clone_export_theory uc th i =
  { uc with muc_theory = Theory.clone_export uc.muc_theory th i }
let add_meta uc m al =
  { uc with muc_theory = Theory.add_meta uc.muc_theory m al }

let create_module ?(path=[]) n =
  use_export_theory (empty_module n path) bool_theory

(** Program decls *)

let add_symbol add id v uc =
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_type uc its =
  add_symbol add_it its.its_pure.ts_name its uc

let add_data uc (its,csl) =
  let add_pls uc pls = add_symbol add_ps pls.pl_ls.ls_name (PL pls) uc in
  let add_proj = option_fold add_pls in
  let add_constr uc (ps,pjl) = List.fold_left add_proj (add_pls uc ps) pjl in
  let uc = add_symbol add_it its.its_pure.ts_name its uc in
  List.fold_left add_constr uc csl

let add_pdecl uc d =
  let uc =  { uc with
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

let add_pdecl_with_tuples uc d =
  let ids = Mid.set_diff d.pd_syms uc.muc_known in
  let ids = Mid.set_diff ids (Theory.get_known uc.muc_theory) in
  let add id s = match is_ts_tuple_id id with
    | Some n -> Sint.add n s
    | None -> s in
  let ixs = Sid.fold add ids Sint.empty in
  let add n uc = use_export_theory uc (tuple_theory n) in
  add_pdecl (Sint.fold add ixs uc) d

(** Clone *)

let clone_export _uc _m _inst =
  assert false (*TODO*)
