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
open Stdlib
open Util
open Ident
open Ty
open Term

(** value types (w/o effects) *)

module rec T : sig

  type varset = {
    vars_tv  : Stv.t;
    vars_reg : Reg.S.t;
  }

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
    ity_vars : varset;
    ity_tag  : Hashweak.tag;
  }

  and ity_node =
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = {
    reg_name  : ident;
    reg_ity   : ity;
  }

end = struct

  type varset = {
    vars_tv  : Stv.t;
    vars_reg : Reg.S.t;
  }

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
    ity_vars : varset;
    ity_tag  : Hashweak.tag;
  }

  and ity_node =
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = {
    reg_name  : ident;
    reg_ity   : ity;
  }

end

and Reg : sig
  module M : Map.S with type key = T.region
  module S : M.Set
  module H : Hashtbl.S with type key = T.region
  module W : Hashweak.S with type key = T.region
end = WeakStructMake (struct
  type t = T.region
  let tag r = r.T.reg_name.id_tag
end)

open T

(** regions *)

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

let reg_equal : region -> region -> bool = (==)
let reg_hash r = id_hash r.reg_name

let create_region id ty = { reg_name = id_register id; reg_ity = ty }

(* variable sets *)

let vars_empty = { vars_tv = Stv.empty ; vars_reg = Sreg.empty }

let vars_union s1 s2 = {
  vars_tv  = Stv.union s1.vars_tv s2.vars_tv;
  vars_reg = Sreg.union s1.vars_reg s2.vars_reg;
}

let create_varset tvs regs = {
  vars_tv = Sreg.fold (fun r -> Stv.union r.reg_ity.ity_vars.vars_tv) regs tvs;
  vars_reg = regs;
}

let rec reg_occurs r vars =
  let check r r' = reg_equal r r' || reg_occurs r r'.reg_ity.ity_vars in
  Sreg.exists (check r) vars.vars_reg

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

  let ity_vars s ity = vars_union s ity.ity_vars
  let reg_vars s r = { s with vars_reg = Sreg.add r s.vars_reg }

  let vars s ity = match ity.ity_node with
    | Ityvar v ->
        { s with vars_tv = Stv.add v s.vars_tv }
    | Itypur (_,tl) ->
        List.fold_left ity_vars s tl
    | Ityapp (_,tl,rl) ->
        List.fold_left reg_vars (List.fold_left ity_vars s tl) rl

  let tag n ity = { ity with
    ity_vars = vars vars_empty ity;
    ity_tag  = Hashweak.create_tag n }

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
  ity_vars = vars_empty;
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
  try ity_s_fold (any_fn pr) (any_fn pts) false ity with FoldSkip -> true

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

let ity_subst_unsafe mv mr ity =
  ity_v_map (fun v -> Mtv.find v mv) (fun r -> Mreg.find r mr) ity

let ity_closed ity = Stv.is_empty ity.ity_vars.vars_tv
let ity_pure ity = Sreg.is_empty ity.ity_vars.vars_reg

(* smart constructors *)

exception BadItyArity of itysymbol * int * int
exception BadRegArity of itysymbol * int * int

exception DuplicateRegion of region
exception UnboundRegion of region

exception RegionMismatch of region * region
exception TypeMismatch of ity * ity

let ity_equal_check ty1 ty2 =
  if not (ity_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))

let reg_equal_check r1 r2 =
  if not (reg_equal r1 r2) then raise (RegionMismatch (r1, r2))

type ity_subst = {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t; (* must preserve ghost-ness *)
}

let ity_subst_empty = {
  ity_subst_tv  = Mtv.empty;
  ity_subst_reg = Mreg.empty;
}

let ity_subst_union s1 s2 =
  let check_ity _ ity1 ity2 = ity_equal_check ity1 ity2; Some ity1 in
  let check_reg _ r1 r2 = reg_equal_check r1 r2; Some r1 in
  { ity_subst_tv  = Mtv.union  check_ity s1.ity_subst_tv  s2.ity_subst_tv;
    ity_subst_reg = Mreg.union check_reg s1.ity_subst_reg s2.ity_subst_reg }

let tv_inst s v = Mtv.find_def (ity_var v) v s.ity_subst_tv
let reg_inst s r = Mreg.find_def r r s.ity_subst_reg

let ity_inst s ity =
  if ity_closed ity && ity_pure ity then ity
  else ity_v_map (tv_inst s) (reg_inst s) ity

let reg_full_inst s r = Mreg.find r s.ity_subst_reg

let ity_full_inst s ity =
  if ity_closed ity && ity_pure ity then ity
  else ity_subst_unsafe s.ity_subst_tv s.ity_subst_reg ity

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
      let id = id_clone r.reg_name in
      let reg = create_region id ity in
      Mreg.add r reg mr, reg

let ity_app_fresh s tl =
  (* type variable map *)
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_args, List.length tl)) in
  (* refresh regions *)
  let mr,rl = Util.map_fold_left (reg_refresh mv) Mreg.empty s.its_regs in
  (* every top region in def is guaranteed to be in mr *)
  match s.its_def with
  | Some ity -> ity_subst_unsafe mv mr ity
  | None -> ity_app s tl rl

let ity_app s tl rl =
  (* type variable map *)
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_args, List.length tl)) in
  (* region map *)
  let sub = { ity_subst_tv = mv; ity_subst_reg = Mreg.empty } in
  let sub = try List.fold_left2 reg_match sub s.its_regs rl
    with Invalid_argument _ ->
      raise (BadRegArity (s, List.length s.its_regs, List.length rl)) in
  (* every type var and top region in def are in its_args and its_regs *)
  match s.its_def with
  | Some ity -> ity_full_inst sub ity
  | None -> ity_app s tl rl

let ity_pur s tl = match s.ts_def with
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let m = try List.fold_left2 add Mtv.empty s.ts_args tl
        with Invalid_argument _ ->
          raise (Ty.BadTypeArity (s, List.length s.ts_args, List.length tl)) in
      ity_subst_unsafe m Mreg.empty (ity_of_ty ty)
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
  (* if a type is an alias then it cannot be abstract or private *)
  if abst && def <> None then Loc.errorm "A type alias cannot be abstract";
  if priv && def <> None then Loc.errorm "A type alias cannot be private";
  { its_pure  = purets;
    its_args  = args;
    its_regs  = regs;
    its_def   = def;
    its_abst  = abst;
    its_priv  = priv }

let ts_unit = ts_tuple 0
let ty_unit = ty_tuple []

let ity_int  = ity_of_ty Ty.ty_int
let ity_bool = ity_of_ty Ty.ty_bool
let ity_unit = ity_of_ty ty_unit

let vars_freeze s =
  let sbs = Stv.fold (fun v -> Mtv.add v (ity_var v)) s.vars_tv Mtv.empty in
  let sbs = { ity_subst_tv = sbs ; ity_subst_reg = Mreg.empty } in
  Sreg.fold (fun r s -> reg_match s r r) s.vars_reg sbs

(** computation types (with effects) *)

(* exception symbols *)
type xsymbol = {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

let xs_equal : xsymbol -> xsymbol -> bool = (==)

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
  eff_reads  : Sreg.t;
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostr : Sreg.t; (* ghost reads *)
  eff_ghostw : Sreg.t; (* ghost writes *)
  eff_ghostx : Sexn.t; (* ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
}

let eff_empty = {
  eff_reads  = Sreg.empty;
  eff_writes = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_ghostr = Sreg.empty;
  eff_ghostw = Sreg.empty;
  eff_ghostx = Sexn.empty;
  eff_resets = Mreg.empty;
}

let eff_is_empty e =
  Sreg.is_empty e.eff_reads &&
  Sreg.is_empty e.eff_writes &&
  Sexn.is_empty e.eff_raises &&
  Sreg.is_empty e.eff_ghostr &&
  Sreg.is_empty e.eff_ghostw &&
  Sexn.is_empty e.eff_ghostx &&
  Mreg.is_empty e.eff_resets

let join_reset _key v1 v2 =
  Some (if option_eq reg_equal v1 v2 then v1 else None)

let eff_union x y = {
  eff_reads  = Sreg.union x.eff_reads  y.eff_reads;
  eff_writes = Sreg.union x.eff_writes y.eff_writes;
  eff_raises = Sexn.union x.eff_raises y.eff_raises;
  eff_ghostr = Sreg.union x.eff_ghostr y.eff_ghostr;
  eff_ghostw = Sreg.union x.eff_ghostw y.eff_ghostw;
  eff_ghostx = Sexn.union x.eff_ghostx y.eff_ghostx;
  eff_resets = Mreg.union join_reset x.eff_resets y.eff_resets;
}

let eff_ghostify e = {
  eff_reads  = Sreg.empty;
  eff_writes = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_ghostr = Sreg.union e.eff_reads  e.eff_ghostr;
  eff_ghostw = Sreg.union e.eff_writes e.eff_ghostw;
  eff_ghostx = Sexn.union e.eff_raises e.eff_ghostx;
  eff_resets = e.eff_resets;
}

let eff_read e ?(ghost=false) r = if ghost
  then { e with eff_ghostr = Sreg.add r e.eff_ghostr }
  else { e with eff_reads  = Sreg.add r e.eff_reads  }

let eff_write e ?(ghost=false) r = if ghost
  then { e with eff_ghostw = Sreg.add r e.eff_ghostw }
  else { e with eff_writes = Sreg.add r e.eff_writes }

let eff_raise e ?(ghost=false) x = if ghost
  then { e with eff_ghostx = Sexn.add x e.eff_ghostx }
  else { e with eff_raises = Sexn.add x e.eff_raises }

let eff_reset e r = { e with eff_resets = Mreg.add r None e.eff_resets }

exception IllegalAlias of region

let eff_assign e ?(ghost=false) r ty =
  let e = eff_write e ~ghost r in
  let sub = ity_match ity_subst_empty r.reg_ity ty in
  (* assignment cannot instantiate type variables *)
  let check tv ity = match ity.ity_node with
    | Ityvar tv' -> tv_equal tv tv'
    | _ -> false in
  if not (Mtv.for_all check sub.ity_subst_tv) then
    raise (TypeMismatch (r.reg_ity,ty));
  (* r:t[r1,r2] <- t[r1,r1] introduces an alias *)
  let add_right _ v s = Sreg.add_new (IllegalAlias v) v s in
  ignore (Mreg.fold add_right sub.ity_subst_reg Sreg.empty);
  (* every region on the rhs must be erased *)
  let add_right k v m = if reg_equal k v then m else Mreg.add v None m in
  let reset = Mreg.fold add_right sub.ity_subst_reg Mreg.empty in
  (* ...except those which occur on the lhs : they are preserved under r *)
  let add_left k v m = if reg_equal k v then m else Mreg.add k (Some r) m in
  let reset = Mreg.fold add_left sub.ity_subst_reg reset in
  { e with eff_resets = Mreg.union join_reset e.eff_resets reset }

let eff_remove_raise e x = { e with
  eff_raises = Sexn.remove x e.eff_raises;
  eff_ghostx = Sexn.remove x e.eff_ghostx;
}

let eff_full_inst s e =
  let s = s.ity_subst_reg in
  (* modified or reset regions in e *)
  let wr = Mreg.map (Util.const ()) e.eff_resets in
  let wr = Sreg.union e.eff_writes wr in
  let wr = Sreg.union e.eff_ghostw wr in
  (* read-only regions in e *)
  let ro = Sreg.diff (Sreg.union e.eff_reads e.eff_ghostr) wr in
  (* all modified or reset regions are instantiated into distinct regions *)
  let add_affected r acc =
    let r = Mreg.find r s in Sreg.add_new (IllegalAlias r) r acc in
  let wr = Sreg.fold add_affected wr Sreg.empty in
  (* all read-only regions are instantiated outside wr *)
  let add_readonly r =
    let r = Mreg.find r s in if Sreg.mem r wr then raise (IllegalAlias r) in
  Sreg.iter add_readonly ro;
  (* calculate instantiated effect *)
  let add_sreg r acc = Sreg.add (Mreg.find r s) acc in
  let add_mreg r v acc =
    Mreg.add (Mreg.find r s) (option_map (fun v -> Mreg.find v s) v) acc in
  { e with
    eff_reads  = Sreg.fold add_sreg e.eff_reads  Sreg.empty;
    eff_writes = Sreg.fold add_sreg e.eff_writes Sreg.empty;
    eff_ghostr = Sreg.fold add_sreg e.eff_ghostr Sreg.empty;
    eff_ghostw = Sreg.fold add_sreg e.eff_ghostw Sreg.empty;
    eff_resets = Mreg.fold add_mreg e.eff_resets Mreg.empty;
  }

let eff_filter vars e =
  let check r = reg_occurs r vars in
  let reset r = function
    | _ when not (check r) -> None
    | Some u as v when check u -> Some v
    | _ -> Some None
  in
  { e with
    eff_reads  = Sreg.filter check e.eff_reads;
    eff_writes = Sreg.filter check e.eff_writes;
    eff_ghostr = Sreg.filter check e.eff_ghostr;
    eff_ghostw = Sreg.filter check e.eff_ghostw;
    eff_resets = Mreg.mapi_filter reset e.eff_resets;
  }

(* program types *)

type vty_value = {
  vtv_ity   : ity;
  vtv_ghost : bool;
  vtv_mut   : region option;
  vtv_vars  : varset;
}

type vty =
  | VTvalue of vty_value
  | VTarrow of vty_arrow

and vty_arrow = {
  vta_arg    : vty_value;
  vta_result : vty;
  vta_effect : effect;
  vta_ghost  : bool;
  vta_vars   : varset;
  (* this varset covers every type variable and region in vta_arg
     and vta_result, but may skip some type variables and regions
     in vta_effect *)
}

(* smart constructors *)

let vty_vars s = function
  | VTvalue vtv -> vars_union s vtv.vtv_vars
  | VTarrow vta -> vars_union s vta.vta_vars

let vty_value ?(ghost=false) ?mut ity =
  let vars = ity.ity_vars in
  let vars = match mut with
    | Some r ->
        ity_equal_check ity r.reg_ity;
        { vars with vars_reg = Sreg.add r vars.vars_reg }
    | None ->
        vars
  in {
    vtv_ity   = ity;
    vtv_ghost = ghost;
    vtv_mut   = mut;
    vtv_vars  = vars;
  }

let vtv_unmut vtv =
  if vtv.vtv_mut = None then vtv else
    vty_value ~ghost:vtv.vtv_ghost vtv.vtv_ity

let vty_ghost = function
  | VTvalue vtv -> vtv.vtv_ghost
  | VTarrow vta -> vta.vta_ghost

let vty_arrow vtv ?(effect=eff_empty) ?(ghost=false) vty =
  (* mutable arguments are rejected outright *)
  if vtv.vtv_mut <> None then
    Loc.errorm "Mutable arguments are not allowed in vty_arrow";
  (* we accept a mutable vty_value as a result to simplify Mlw_expr,
     but erase it in the signature: only projections return mutables *)
  let vty = match vty with
    | VTvalue v -> VTvalue (vtv_unmut v)
    | VTarrow _ -> vty
  in {
    vta_arg    = vtv;
    vta_result = vty;
    vta_effect = effect;
    vta_ghost  = ghost || vty_ghost vty;
    vta_vars   = vty_vars vtv.vtv_vars vty;
  }

let vtv_ghostify vtv = { vtv with vtv_ghost = true }
let vta_ghostify vta = { vta with vta_ghost = true }

let vty_ghostify = function
  | VTvalue vtv -> VTvalue (vtv_ghostify vtv)
  | VTarrow vta -> VTarrow (vta_ghostify vta)

let vty_app_arrow vta vtv =
  ity_equal_check vta.vta_arg.vtv_ity vtv.vtv_ity;
  let ghost = vta.vta_ghost || (vtv.vtv_ghost && not vta.vta_arg.vtv_ghost) in
  let result = if ghost then vty_ghostify vta.vta_result else vta.vta_result in
  let effect =
    if vty_ghost result then eff_ghostify vta.vta_effect else vta.vta_effect in
    (* we don't really need this, because Mlw_expr will ensure that the effect
       of every ghost expression is properly ghostified *)
  effect, result

(* vty instantiation *)

let vtv_full_inst s vtv =
  vty_value ~ghost:vtv.vtv_ghost (ity_full_inst s vtv.vtv_ity)

(* the substitution must cover not only vta.vta_tvs and vta.vta_regs
   but also every type variable and every region in vta_effect *)
let rec vta_full_inst s vta =
  let vtv = vtv_full_inst s vta.vta_arg in
  let vty = vty_full_inst s vta.vta_result in
  let eff = eff_full_inst s vta.vta_effect in
  vty_arrow ~ghost:vta.vta_ghost ~effect:eff vtv vty

and vty_full_inst s = function
  | VTvalue vtv -> VTvalue (vtv_full_inst s vtv)
  | VTarrow vta -> VTarrow (vta_full_inst s vta)

let rec vta_filter vars a =
  let vars = vars_union vars a.vta_arg.vtv_vars in
  let vty, vars = match a.vta_result with
    (* FIXME? We allow effects on the regions from a VTvalue result,
       but only reset is actually meaningful. Should we require that
       any new region in the result be reset? *)
    | VTvalue v -> a.vta_result, vars_union vars v.vtv_vars
    | VTarrow a -> VTarrow (vta_filter vars a), vars in
  let effect = eff_filter vars a.vta_effect in
  vty_arrow ~ghost:a.vta_ghost ~effect a.vta_arg vty

(** THE FOLLOWING CODE MIGHT BE USEFUL LATER FOR WPgen *)
(*
(* program variables *)
type pvsymbol = {
  pv_vs      : vsymbol;
  pv_ity     : ity;
  pv_ghost   : bool;
  pv_mutable : region option;
  pv_tvs     : Stv.t;
  pv_regs    : Sreg.t;
}

module Pv = StructMake (struct
  type t = pvsymbol
  let tag pv = Hashweak.tag_hash pv.pv_vs.vs_name.id_tag
end)

module Spv = Pv.S
module Mpv = Pv.M

let pv_equal : pvsymbol -> pvsymbol -> bool = (==)

exception InvalidPVsymbol of ident

let create_pvsymbol id ?mut ?(ghost=false) ity =
  let ty = ty_of_ity ity in
  let vs = create_vsymbol id ty in
  begin match mut with
    | Some r when
      (* A ghost variable may contain a non-ghost region.
         No writes are allowed in such a ghost variable. *)
      not (ity_equal r.reg_ity ity) || (r.reg_ghost && not ghost) ->
        raise (InvalidPVsymbol vs.vs_name)
    | _ ->
        ()
  end;
  let tvs = ity_freevars Stv.empty ity in
  let regs = ity_topregions Sreg.empty ity in
  let regs = option_fold (fun s r -> Sreg.add r s) regs mut in
  { pv_vs      = vs;
    pv_ity     = ity;
    pv_ghost   = ghost;
    pv_mutable = mut;
    pv_tvs     = tvs;
    pv_regs    = regs;
  }

let pv_clone pv =
  let id = id_clone pv.pv_vs.vs_name in
  let vs = create_vsymbol id pv.pv_vs.vs_ty in
  { pv with pv_vs = vs }

let pv_full_inst s pv =
  let ghost = pv.pv_ghost in
  let mut = option_map (reg_full_inst s) pv.pv_mutable in
  let ity = ity_full_inst s pv.pv_ity in
  create_pvsymbol (id_clone pv.pv_vs.vs_name) ~ghost ?mut ity

(* value types *)

type vty =
  | VTvalue of pvsymbol
  | VTarrow of vty_arrow

(* computation types *)
and vty_arrow = {
  a_arg   : pvsymbol;
  a_vty   : vty;
  a_eff   : effect;
  a_pre   : term; (* epsilon under a dummy variable, to accumulate substs *)
  a_post  : term; (* epsilon under the value variable or under a dummy vs *)
  a_xpost : term Mexn.t; (* epsilon under the exception value variable *)
  a_tvs   : Stv.t; (* we do not count type variables in eff/pre/post/xpost *)
  a_regs  : Sreg.t; (* we do not count regions in eff/pre/post/xpost *)
}

type pre = term
type post = term
type xpost = (vsymbol * post) Mexn.t

type vty_comp = {
  c_vty   : vty;
  c_eff   : effect;
  c_pre   : pre;
  c_post  : post;
  c_xpost : xpost;
}

let vty_freevars s = function
  | VTvalue pv -> Stv.union s pv.pv_tvs
  | VTarrow a  -> Stv.union s a.a_tvs

let vty_topregions s = function
  | VTvalue pv -> Sreg.union s pv.pv_regs
  | VTarrow a  -> Sreg.union s a.a_regs

(* smart constructors *)

let vty_value pvs = VTvalue pvs

exception InvalidExceptionPost of xsymbol

(* this vs is used to close pre- and post-conditions in order
   to accumulate substitutions into a_arg pvsymbols *)

let close_spec =
  let dummy = create_vsymbol (id_fresh "dummy") ty_int in
  let dumbf = t_eps_close dummy t_true in
  function
    | { t_node = Ttrue } -> dumbf
    | f -> t_eps_close dummy f

let open_spec = function
  | { t_node = Teps bf } -> t_open_bound bf
  | _ -> assert false

let vty_arrow
  x ?(pre=t_true) ?(post=t_true) ?(xpost=Mexn.empty) ?(effect=eff_empty) vty =
  (* check for clashes *)
(* let check_vs y = if vs_equal x.pv_vs y then raise (DuplicateVar y) in *)
  let check_pv y = if pv_equal x y then raise (DuplicateVar x.pv_vs) in
  let rec check = function
    | VTarrow a ->
     (* Mexn.iter (fun _ (y,_) -> check_vs y) a.a_xpost; *)
        check_pv a.a_arg;
        check a.a_vty
    | VTvalue y ->
        check_pv y
  in
  check vty;
  (* check that every raised exception is mentioned in xpost *)
  if not (Mexn.set_submap effect.eff_raises xpost) then
    (let d = Mexn.set_diff xpost effect.eff_raises in
    raise (InvalidExceptionPost (fst (Mexn.choose d))));
  (* check that every exception mentioned in xpost is raised *)
  if not (Mexn.set_submap xpost effect.eff_raises) then
    (let d = Mexn.set_diff effect.eff_raises xpost in
    raise (InvalidExceptionPost (fst (Mexn.choose d))));
  (* check that vsymbols in xpost have valid types *)
  let conv_xpost xs (vs,f) =
    if not (ty_equal (ty_of_ity xs.xs_ity) vs.vs_ty)
    then raise (InvalidExceptionPost xs);
    (* check_vs vs; *)
    t_eps_close vs f
  in
  let post = match vty with
    | VTvalue pv -> t_eps_close pv.pv_vs post
    | VTarrow _  -> close_spec post
  in
  VTarrow {
    a_arg   = x;
    a_vty   = vty;
    a_eff   = effect;
    a_pre   = close_spec pre;
    a_post  = post;
    a_xpost = Mexn.mapi conv_xpost xpost;
    a_tvs   = vty_freevars x.pv_tvs vty;
    a_regs  = vty_topregions x.pv_regs vty;
  }

(*
exception NotAFunction

let get_arrow = function
  | VTvalue _ -> raise NotAFunction
  | VTarrow a -> a
*)

let vty_app_arrow arr x =
  ity_equal_check arr.a_arg.pv_ity x.pv_ity;
  let subst f = t_subst_single arr.a_arg.pv_vs (t_var x.pv_vs) f in
  let _,pre = open_spec (subst arr.a_pre) in
  let res,post = open_spec (subst arr.a_post) in
  let xsubst e = open_spec (subst e) in
  let rec arr_subst arr = { arr with
    a_vty   = (match arr.a_vty with
      | VTarrow a -> VTarrow (arr_subst a)
      | VTvalue _ -> arr.a_vty);
    a_pre   = subst arr.a_pre;
    a_post  = subst arr.a_post;
    a_xpost = Mexn.map subst arr.a_xpost;
  }
  in
  let vty = match arr.a_vty with
    (* here we make a new pvsymbol in a bad fashion. It should however
       be safe, since res comes from t_open_bound and is guaranteed to
       be fresh, so there can be no illegal sharing of idents *)
    | VTvalue pv -> VTvalue { pv with pv_vs = res }
    | VTarrow a  -> VTarrow (arr_subst a)
  in {
    c_vty   = vty;
    c_eff   = arr.a_eff;
    c_pre   = pre;
    c_post  = post;
    c_xpost = Mexn.map xsubst arr.a_xpost;
  }

let open_vty_arrow arr =
  let pv = pv_clone arr.a_arg in
  let c = vty_app_arrow arr pv in
  pv, c.c_vty

let vty_full_inst s vty =
  let subT = Mtv.map ty_of_ity s.ity_subst_tv in
  let rec inst subV = function
    | VTvalue pv ->
        (* this is not the same vsymbol anymore that is bound in
           the preceding post. However, this should not matter. *)
        VTvalue (pv_full_inst s pv)
    | VTarrow a ->
        let x = pv_full_inst s a.a_arg in
        let subV = Mvs.add a.a_arg.pv_vs (t_var x.pv_vs) subV in
        let subst = t_ty_subst subT subV in
        let vty = inst subV a.a_vty in
        VTarrow {
          a_arg   = x;
          a_vty   = vty;
          a_eff   = eff_full_inst s a.a_eff;
          a_pre   = subst a.a_pre;
          a_post  = subst a.a_post;
          a_xpost = Mexn.map subst a.a_xpost;
          a_tvs   = vty_freevars x.pv_tvs vty;
          a_regs  = vty_topregions x.pv_regs vty;
        }
  in
  inst Mvs.empty vty
*)
