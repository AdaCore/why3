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

(** value types (w/o effects) *)

type itysymbol = {
  its_pure : tysymbol;
  its_args : tvsymbol list;
  its_regs : region   list;
  its_def  : ity option;
  its_abst : bool;
  its_priv : bool;
}

and ity = {
  ity_node : ity_node;
  ity_tag  : Hashweak.tag;
}

and ity_node =
  | Ityvar of tvsymbol
  | Itypur of tysymbol * ity list
  | Ityapp of itysymbol * ity list * region list

and region = {
  reg_name  : ident;
  reg_ity   : ity;
  reg_ghost : bool;
}

(** regions *)

module Reg = WeakStructMake (struct
  type t = region
  let tag r = r.reg_name.id_tag
end)

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

let reg_equal : region -> region -> bool = (==)
let reg_hash r = id_hash r.reg_name

let create_region id ?(ghost=false) ty =
  { reg_name = id_register id; reg_ity = ty; reg_ghost = ghost }

(* value type symbols *)

module Itsym = WeakStructMake (struct
  type t = itysymbol
  let tag its = its.its_pure.ts_name.id_tag
end)

module Sits = Itsym.S
module Mits = Itsym.M
module Hits = Itsym.H
module Wits = Itsym.W

let its_equal : itysymbol -> itysymbol -> bool = (==)
let ity_equal : ity       -> ity       -> bool = (==)

let its_hash its = id_hash its.its_pure.ts_name
let ity_hash ity = Hashweak.tag_hash ity.ity_tag

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Ityvar n1, Ityvar n2 ->
        tv_equal n1 n2
    | Itypur (s1,l1), Itypur (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 ity_equal l1 l2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 && List.for_all2 ity_equal l1 l2
          && List.for_all2 reg_equal r1 r2
    | _ ->
        false

  let hash ity = match ity.ity_node with
    | Ityvar v -> tv_hash v
    | Itypur (s,tl) -> Hashcons.combine_list ity_hash (ts_hash s) tl
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list reg_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl

  let tag n ity = { ity with ity_tag = Hashweak.create_tag n }
end)

module Ity = WeakStructMake (struct
  type t = ity
  let tag ity = ity.ity_tag
end)

module Sity = Ity.S
module Mity = Ity.M
module Hity = Ity.H
module Wity = Ity.W

let mk_ity n = {
  ity_node = n;
  ity_tag  = Hashweak.dummy_tag;
}

let ity_var n = Hsity.hashcons (mk_ity (Ityvar n))
let ity_pur s tl = Hsity.hashcons (mk_ity (Itypur (s,tl)))
let ity_app s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))

(* generic traversal functions *)

let ity_map fn ity = match ity.ity_node with
  | Ityvar _ -> ity
  | Itypur (f,tl) -> ity_pur f (List.map fn tl)
  | Ityapp (f,tl,rl) -> ity_app f (List.map fn tl) rl

let ity_fold fn acc ity = match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (_,tl)
  | Ityapp (_,tl,_) -> List.fold_left fn acc tl

let ity_all pr ity =
  try ity_fold (all_fn pr) true ity with FoldSkip -> false

let ity_any pr ity =
  try ity_fold (any_fn pr) false ity with FoldSkip -> true

(* symbol-wise map/fold *)

let rec ity_s_fold fn fts acc ity = match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (ts, tl) -> List.fold_left (ity_s_fold fn fts) (fts acc ts) tl
  | Ityapp (f, tl, rl) ->
      let acc = List.fold_left (ity_s_fold fn fts) (fn acc f) tl in
      List.fold_left (fun acc r -> ity_s_fold fn fts acc r.reg_ity) acc rl

let ity_s_all pr pts ity =
  try ity_s_fold (all_fn pr) (all_fn pts) true ity with FoldSkip -> false

let ity_s_any pr pts ity =
  try ity_s_fold (any_fn pr) (all_fn pts) false ity with FoldSkip -> true

(* traversal functions on type variables and regions *)

let rec ity_v_map fnv fnr ity = match ity.ity_node with
  | Ityvar v ->
      fnv v
  | Itypur (f,tl) ->
      ity_pur f (List.map (ity_v_map fnv fnr) tl)
  | Ityapp (f,tl,rl) ->
      ity_app f (List.map (ity_v_map fnv fnr) tl) (List.map fnr rl)

let rec ity_v_fold fnv fnr acc ity = match ity.ity_node with
  | Ityvar v ->
      fnv acc v
  | Itypur (_,tl) ->
      List.fold_left (ity_v_fold fnv fnr) acc tl
  | Ityapp (_,tl,rl) ->
      List.fold_left (ity_v_fold fnv fnr) (List.fold_left fnr acc rl) tl

let ity_v_all prv prr ity =
  try ity_v_fold (all_fn prv) (all_fn prr) true ity with FoldSkip -> false

let ity_v_any prv prr ity =
  try ity_v_fold (any_fn prv) (any_fn prr) false ity with FoldSkip -> true

let ity_full_inst mv mr ity =
  ity_v_map (fun v -> Mtv.find v mv) (fun r -> Mreg.find r mr) ity

let ity_freevars = ity_v_fold (fun s v -> Stv.add v s) Util.const
let ity_topregions = ity_v_fold Util.const (fun s r -> Sreg.add r s)

let ity_closed = ity_v_all Util.ffalse Util.ttrue
let ity_pure = ity_v_all Util.ttrue Util.ffalse

(* smart constructors *)

exception BadItyArity of itysymbol * int * int
exception BadRegArity of itysymbol * int * int

exception DuplicateRegion of region
exception UnboundRegion of region
exception InvalidRegion of region

exception RegionMismatch of region * region
exception TypeMismatch of ity * ity

let ity_equal_check ty1 ty2 =
  if not (ity_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))

type ity_subst = {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t;
}

let ity_subst_empty = {
  ity_subst_tv = Mtv.empty;
  ity_subst_reg = Mreg.empty;
}

let ity_inst s ity =
  ity_v_map
    (fun v -> Mtv.find_def (ity_var v) v s.ity_subst_tv)
    (fun r -> Mreg.find_def r r s.ity_subst_reg)
    ity

let rec ity_match s ity1 ity2 =
  let set = function
    | None -> Some ity2
    | Some ity3 as r when ity_equal ity3 ity2 -> r
    | _ -> raise Exit
  in
  match ity1.ity_node, ity2.ity_node with
  | Ityapp (s1, l1, r1), Ityapp (s2, l2, r2) when its_equal s1 s2 ->
      let s = List.fold_left2 ity_match s l1 l2 in
      List.fold_left2 reg_match s r1 r2
  | Itypur (s1, l1), Itypur (s2, l2) when ts_equal s1 s2 ->
      List.fold_left2 ity_match s l1 l2
  | Ityvar tv1, _ ->
      { s with ity_subst_tv = Mtv.change set tv1 s.ity_subst_tv }
  | _ ->
      raise Exit

and reg_match s r1 r2 =
  let is_new = ref false in
  let set = function
    | None -> is_new := true; Some r2
    | Some r3 as r when reg_equal r3 r2 -> r
    | _ -> raise Exit
  in
  let reg_map = Mreg.change set r1 s.ity_subst_reg in
  let s = { s with ity_subst_reg = reg_map } in
  if !is_new then ity_match s r1.reg_ity r2.reg_ity else s

let ity_match s ity1 ity2 =
  try ity_match s ity1 ity2
  with Exit -> raise (TypeMismatch (ity_inst s ity1, ity2))

let rec ty_of_ity ity = match ity.ity_node with
  | Ityvar v -> ty_var v
  | Itypur (s,tl) -> ty_app s (List.map ty_of_ity tl)
  | Ityapp (s,tl,_) -> ty_app s.its_pure (List.map ty_of_ity tl)

let rec ity_of_ty ty = match ty.ty_node with
  | Tyvar v -> ity_var v
  | Tyapp (s,tl) -> ity_pur s (List.map ity_of_ty tl)

let rec ity_inst_fresh mv mr ity = match ity.ity_node with
  | Ityvar v ->
      mr, Mtv.find v mv
  | Itypur (s,tl) ->
      let mr,tl = Util.map_fold_left (ity_inst_fresh mv) mr tl in
      mr, ity_pur s tl
  | Ityapp (s,tl,rl) ->
      let mr,tl = Util.map_fold_left (ity_inst_fresh mv) mr tl in
      let mr,rl = Util.map_fold_left (reg_refresh mv) mr rl in
      mr, ity_app s tl rl

and reg_refresh mv mr r = match Mreg.find_opt r mr with
  | Some r ->
      mr, r
  | None ->
      let mr,ity = ity_inst_fresh mv mr r.reg_ity in
      let id = id_clone r.reg_name and ghost = r.reg_ghost in
      let reg = create_region id ~ghost ity in
      Mreg.add r reg mr, reg

let ity_app_fresh s tl =
  (* type variable map *)
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_args, List.length tl)) in
  (* refresh regions *)
  let mr,rl = Util.map_fold_left (reg_refresh mv) Mreg.empty s.its_regs in
  (* every external region in def is guaranteed to be in mr *)
  match s.its_def with
  | Some ity -> ity_full_inst mv mr ity
  | None -> ity_app s tl rl

let ity_app s tl rl =
  (* type variable map *)
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_args, List.length tl)) in
  (* region map *)
  let add m v r = Mreg.add v r m in
  let mr = try List.fold_left2 add Mreg.empty s.its_regs rl
    with Invalid_argument _ ->
      raise (BadRegArity (s, List.length s.its_regs, List.length rl)) in
  (* check that region types do unify *)
  let sub = { ity_subst_tv = mv; ity_subst_reg = mr } in
  let rmatch sub r1 r2 = ity_match sub r1.reg_ity r2.reg_ity in
  ignore (List.fold_left2 rmatch sub s.its_regs rl);
  (* to instantiate def, mv and mr are enough *)
  match s.its_def with
  | Some ity -> ity_full_inst mv mr ity
  | None -> ity_app s tl rl

let ity_pur s tl = match s.ts_def with
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let m = List.fold_left2 add Mtv.empty s.ts_args tl in
      ity_full_inst m Mreg.empty (ity_of_ty ty)
  | None ->
      ity_pur s tl

let create_itysymbol name ?(abst=false) ?(priv=false) args regs def =
  let puredef = option_map ty_of_ity def in
  let purets = create_tysymbol name args puredef in
  (* all regions *)
  let add s v = Sreg.add_new (DuplicateRegion v) v s in
  let sregs = List.fold_left add Sreg.empty regs in
  (* all type variables *)
  let sargs = List.fold_right Stv.add args Stv.empty in
  (* all type variables in [regs] must be in [args] *)
  let check tv = Stv.mem tv sargs || raise (UnboundTypeVar tv) in
  List.iter (fun r -> ignore (ity_v_all check Util.ttrue r.reg_ity)) regs;
  (* all regions in [def] must be in [regs] *)
  let check r = Sreg.mem r sregs || raise (UnboundRegion r) in
  ignore (option_map (ity_v_all Util.ttrue check) def);
  (* if a type is an alias then abst and priv will be ignored *)
  { its_pure  = purets;
    its_args  = args;
    its_regs  = regs;
    its_def   = def;
    its_abst  = abst;
    its_priv  = priv }

(** computation types (with effects) *)

(* exception symbols *)
type xsymbol = {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

let create_xsymbol id ity =
  let id = id_register id in
  if not (ity_closed ity) then raise (PolymorphicException (id, ity));
  if not (ity_pure ity) then raise (MutableException (id, ity));
  { xs_name = id; xs_ity = ity; }

module Exn = StructMake (struct
  type t = xsymbol
  let tag xs = Hashweak.tag_hash xs.xs_name.id_tag
end)

module Sexn = Exn.S
module Mexn = Exn.M

(* effects *)
type effect = {
  eff_reads   : Sreg.t;
  eff_writes  : Sreg.t;
  eff_erases  : Sreg.t;
  eff_renames : region Mreg.t; (* if r1->r2 then r1 appears in ty(r2) *)
  eff_raises  : Sexn.t;
}

let eff_empty = {
  eff_reads   = Sreg.empty;
  eff_writes  = Sreg.empty;
  eff_erases  = Sreg.empty;
  eff_renames = Mreg.empty;
  eff_raises  = Sexn.empty
}

let eff_union x y =
  let e = Sreg.union x.eff_erases y.eff_erases in
  let rx = Mreg.diff (fun _ _ _ -> None) x.eff_renames e in
  let ry = Mreg.diff (fun _ _ _ -> None) y.eff_renames e in
  let rn = Mreg.union
      (fun _ r1 r2 -> if reg_equal r1 r2 then Some r1 else None) rx ry in
  let re = Mreg.inter
      (fun _ r1 r2 -> if reg_equal r1 r2 then None else Some ()) rx ry in
  { eff_reads = Sreg.union x.eff_reads y.eff_reads;
    eff_writes = Sreg.union x.eff_writes y.eff_writes;
    eff_erases = Sreg.union e re;
    eff_renames = rn;
    eff_raises = Sexn.union x.eff_raises y.eff_raises; }

let eff_read r = { eff_empty with eff_reads = Sreg.singleton r }
let eff_write r = { eff_empty with eff_writes = Sreg.singleton r }
let eff_erase r = { eff_empty with eff_erases = Sreg.singleton r }
let eff_raise xs = { eff_empty with eff_raises = Sexn.singleton xs }
let eff_remove_raise xs e = { e with eff_raises = Sexn.remove xs e.eff_raises }

(* program variables *)
type pvsymbol = {
  pv_vs      : vsymbol;
  pv_ity     : ity;
  pv_ghost   : bool;
  pv_mutable : region option;
}

exception InvalidPVsymbol of ident

let create_pvsymbol id ?mut ?(ghost=false) ity =
  let ty = ty_of_ity ity in
  let vs = create_vsymbol id ty in
  begin match mut with
    | Some r when not (ity_equal r.reg_ity ity) || ghost <> r.reg_ghost ->
        raise (InvalidPVsymbol vs.vs_name)
    | _ ->
        ()
  end;
  { pv_vs = vs;
    pv_ity = ity;
    pv_ghost = ghost;
    pv_mutable = mut; }

let pv_equal : pvsymbol -> pvsymbol -> bool = (==)

(* value types *)
type vty =
  | VTvalue of pvsymbol
  | VTarrow of pvsymbol * cty

(* computation types *)
and cty = {
  c_pre   : term;
  c_vty   : vty;
  c_eff   : effect;
  c_post  : term;
  c_xpost : xpost;
}

and xpost = (pvsymbol * term) Mexn.t

(* smart constructors *)
let create_cty
  ?(pre=t_true) ?(post=t_true) ?(xpost=Mexn.empty) ?(effect=eff_empty) vty =
  { c_pre = pre;
    c_vty = vty;
    c_eff = effect;
    c_post = post;
    c_xpost = xpost; }

let vty_value pvs = VTvalue pvs

let vty_arrow x cty =
  (* check that x does not appear in cty *)
  let rec check = function
    | VTvalue y -> if pv_equal x y then raise (DuplicateVar x.pv_vs)
    | VTarrow (y, c) ->
        if pv_equal x y then raise (DuplicateVar x.pv_vs); check c.c_vty
  in
  check cty.c_vty;
  VTarrow (x, cty)
