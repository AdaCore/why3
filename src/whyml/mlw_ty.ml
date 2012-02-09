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

(** value types (w/o effects) *)

type vtysymbol = {
  vts_pure  : tysymbol;
  vts_args  : tvsymbol list;
  vts_regs  : region   list;
  vts_def   : vty option;
}

and vty = {
  vty_node : vty_node;
  vty_tag  : Hashweak.tag;
}

and vty_node =
  | Vtyvar of tvsymbol
  | Vtypur of tysymbol * vty list
  | Vtyapp of vtysymbol * vty list * region list
  (* | Vtymod of tysymbol * vty *)

and region = {
  reg_ty  : vty;
  reg_tag : Hashweak.tag;
}

(** regions *)

module Reg = WeakStructMake (struct
  type t = region
  let tag r = r.reg_tag
end)

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

let reg_equal : region -> region -> bool = (==)
let reg_hash r = Hashweak.tag_hash r.reg_tag

let create_region =
  let r = ref 0 in
  fun ty ->
    incr r;
    { reg_ty = ty; reg_tag = Hashweak.create_tag !r }

(* value type symbols *)

module VTsym = WeakStructMake (struct
  type t = vtysymbol
  let tag vts = vts.vts_pure.ts_name.id_tag
end)

module Svts = VTsym.S
module Mvts = VTsym.M
module Hvts = VTsym.H
module Wvts = VTsym.W

let vts_equal : vtysymbol -> vtysymbol -> bool = (==)
let vty_equal : vty       -> vty       -> bool = (==)

let vts_hash vts = id_hash vts.vts_pure.ts_name
let vty_hash vty = Hashweak.tag_hash vty.vty_tag

module Hsvty = Hashcons.Make (struct
  type t = vty

  let equal vty1 vty2 = match vty1.vty_node, vty2.vty_node with
    | Vtyvar n1, Vtyvar n2 ->
        tv_equal n1 n2
    | Vtypur (s1,l1), Vtypur (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 vty_equal l1 l2
    | Vtyapp (s1,l1,r1), Vtyapp (s2,l2,r2) ->
        vts_equal s1 s2 && List.for_all2 vty_equal l1 l2
          && List.for_all2 reg_equal r1 r2
    (* | Vtymod (s1, vty1), Vtymod (s2, vty2) -> *)
    (*     ts_equal s1 s2 && vty_equal vty1 vty2 *)
    | _ ->
        false

  let hash vty = match vty.vty_node with
    | Vtyvar v -> tv_hash v
    | Vtypur (s,tl) -> Hashcons.combine_list vty_hash (ts_hash s) tl
    | Vtyapp (s,tl,rl) ->
        Hashcons.combine_list reg_hash
          (Hashcons.combine_list vty_hash (vts_hash s) tl) rl
    (* | Vtymod (ts, vty) -> *)
    (*     Hashcons.combine (ts_hash ts) (vty_hash vty) *)

  let tag n vty = { vty with vty_tag = Hashweak.create_tag n }
end)

module Vty = WeakStructMake (struct
  type t = vty
  let tag vty = vty.vty_tag
end)

module Svty = Vty.S
module Mvty = Vty.M
module Hvty = Vty.H
module Wvty = Vty.W

let mk_vty n = {
  vty_node = n;
  vty_tag  = Hashweak.dummy_tag;
}

let vty_var n = Hsvty.hashcons (mk_vty (Vtyvar n))
let vty_pur s tl = Hsvty.hashcons (mk_vty (Vtypur (s,tl)))
let vty_app s tl rl = Hsvty.hashcons (mk_vty (Vtyapp (s,tl,rl)))
(* let vty_mod ts vty = Hsvty.hashcons (mk_vty (Vtymod (ts,vty))) *)

(* generic traversal functions *)

let vty_map fn vty = match vty.vty_node with
  | Vtyvar _ -> vty
  | Vtypur (f,tl) -> vty_pur f (List.map fn tl)
  | Vtyapp (f,tl,rl) -> vty_app f (List.map fn tl) rl
  (* | Vtymod (ts, vty) -> vty_mod ts (fn vty) *)

let vty_fold fn acc vty = match vty.vty_node with
  | Vtyvar _ -> acc
  | Vtypur (_,tl)
  | Vtyapp (_,tl,_) -> List.fold_left fn acc tl
  (* | Vtymod (_,vty) -> fn acc vty *)

let vty_all pr vty =
  try vty_fold (all_fn pr) true vty with FoldSkip -> false

let vty_any pr vty =
  try vty_fold (any_fn pr) false vty with FoldSkip -> true

(* traversal functions on type variables and regions *)

let rec vty_v_map fnv fnr vty = match vty.vty_node with
  | Vtyvar v ->
      fnv v
  | Vtypur (f,tl) ->
      vty_pur f (List.map (vty_v_map fnv fnr) tl)
  | Vtyapp (f,tl,rl) ->
      vty_app f (List.map (vty_v_map fnv fnr) tl) (List.map fnr rl)
  (* | Vtymod (ts, vty) -> *)
  (*     vty_mod ts (vty_v_map fnv fnr vty) *)

let rec vty_v_fold fnv fnr acc vty = match vty.vty_node with
  | Vtyvar v ->
      fnv acc v
  | Vtypur (_,tl) ->
      List.fold_left (vty_v_fold fnv fnr) acc tl
  | Vtyapp (_,tl,rl) ->
      List.fold_left (vty_v_fold fnv fnr) (List.fold_left fnr acc rl) tl
  (* | Vtymod (_, vty) -> *)
  (*     vty_v_fold fnv fnr acc vty *)

let vty_v_all prv prr vty =
  try vty_v_fold (all_fn prv) (all_fn prr) true vty with FoldSkip -> false

let vty_v_any prv prr vty =
  try vty_v_fold (any_fn prv) (any_fn prr) false vty with FoldSkip -> true

let vty_full_inst mv mr vty =
  vty_v_map (fun v -> Mtv.find v mv) (fun r -> Mreg.find r mr) vty

let vty_freevars s vty = vty_v_fold (fun s v -> Stv.add v s) Util.const s vty

let vty_closed vty = vty_v_all Util.ffalse Util.ttrue vty
let vty_pure vty = vty_v_all Util.ttrue Util.ffalse vty

(* smart constructors *)

exception BadVtyArity of vtysymbol * int * int
exception BadRegArity of vtysymbol * int * int

exception DuplicateRegion of region
exception UnboundRegion of region
exception InvalidRegion of region

exception RegionMismatch of region * region
exception TypeMismatch of vty * vty

let vty_equal_check ty1 ty2 =
  if not (vty_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))

type vty_subst = {
  vty_subst_tv:  vty Mtv.t;
  vty_subst_reg: region Mreg.t;
}

let vty_subst_empty = {
  vty_subst_tv = Mtv.empty;
  vty_subst_reg = Mreg.empty;
}

let vty_inst s vty =
  vty_v_map
    (fun v -> Mtv.find_default v (vty_var v) s.vty_subst_tv)
    (fun r -> Mreg.find_default r r s.vty_subst_reg)
    vty

let rec vty_match s vty1 vty2 =
  let set = function
    | None -> Some vty2
    | Some vty3 as r when vty_equal vty3 vty2 -> r
    | _ -> raise Exit
  in
  match vty1.vty_node, vty2.vty_node with
  | Vtyapp (s1, l1, r1), Vtyapp (s2, l2, r2) when vts_equal s1 s2 ->
      let s = List.fold_left2 vty_match s l1 l2 in
      List.fold_left2 reg_match s r1 r2
  | Vtypur (s1, l1), Vtypur (s2, l2) when ts_equal s1 s2 ->
      List.fold_left2 vty_match s l1 l2
  (* | Vtymod (s1, vty1), Vtymod (s2, vty2) when ts_equal s1 s2 -> *)
  (*     vty_match s vty1 vty2 *)
  | Vtyvar tv1, _ ->
      { s with vty_subst_tv = Mtv.change tv1 set s.vty_subst_tv }
  | _ ->
      raise Exit

and reg_match s r1 r2 =
  let is_new = ref false in
  let set = function
    | None -> is_new := true; Some r2
    | Some r3 as r when reg_equal r3 r2 -> r
    | _ -> raise Exit
  in
  let reg_map = Mreg.change r1 set s.vty_subst_reg in
  let s = { s with vty_subst_reg = reg_map } in
  if !is_new then vty_match s r1.reg_ty r2.reg_ty else s

let vty_match s vty1 vty2 =
  try vty_match s vty1 vty2
  with Exit -> raise (TypeMismatch (vty_inst s vty1, vty2))

let rec ty_of_vty vty = match vty.vty_node with
  | Vtyvar v -> ty_var v
  | Vtypur (s,tl) -> ty_app s (List.map ty_of_vty tl)
  | Vtyapp (s,tl,_) -> ty_app s.vts_pure (List.map ty_of_vty tl)
  (* | Vtymod (_,vty) -> ty_of_vty vty *)

let rec vty_of_ty ty = match ty.ty_node with
  | Tyvar v -> vty_var v
  | Tyapp (s,tl) -> vty_pur s (List.map vty_of_ty tl)

let vty_app s tl rl =
  let tll = List.length tl in
  let rll = List.length rl in
  let stl = List.length s.vts_args in
  let srl = List.length s.vts_regs in
  if tll <> stl then raise (BadVtyArity (s,stl,tll));
  if rll <> srl then raise (BadRegArity (s,srl,rll));
  let add m v t = Mtv.add v t m in
  let mv = List.fold_left2 add Mtv.empty s.vts_args tl in
  let add m v r = Mreg.add v r m in
  let mr = List.fold_left2 add Mreg.empty s.vts_regs rl in
  (* check that region types do unify *)
  let sub = { vty_subst_tv = mv; vty_subst_reg = mr } in
  let rmatch sub r1 r2 = vty_match sub r1.reg_ty r2.reg_ty in
  ignore (List.fold_left2 rmatch sub s.vts_regs rl);
  (* to instantiate def, mv and mr are enough *)
  match s.vts_def with
  | Some vty ->
      vty_full_inst mv mr vty
  | None ->
      vty_app s tl rl

(* let rec vty_unmod vty = match vty.vty_node with *)
(*   | Vtyvar _ -> vty *)
(*   | Vtypur (s,tl) -> vty_pur s (List.map vty_unmod tl) *)
(*   | Vtyapp (s,tl,rl) -> vty_app s (List.map vty_unmod tl) rl *)
(*   | Vtymod (_,vty) -> vty_unmod vty *)

let vty_pur s tl = match s.ts_def with
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let m = List.fold_left2 add Mtv.empty s.ts_args tl in
      vty_full_inst m Mreg.empty (vty_of_ty ty)
  | None ->
      vty_pur s tl

let create_vtysymbol name args regs def (* model *) =
  let puredef = option_map ty_of_vty def in
  let purets = create_tysymbol name args puredef in
  (* all regions *)
  let add s v = Sreg.add_new v (DuplicateRegion v) s in
  let sregs = List.fold_left add Sreg.empty regs in
  (* all type variables *)
  let sargs = List.fold_right Stv.add args Stv.empty in
  (* all type variables in [regs] must be in [args] *)
  let check tv = Stv.mem tv sargs || raise (UnboundTypeVar tv) in
  List.iter (fun r -> ignore (vty_v_all check Util.ttrue r.reg_ty)) regs;
  (* all regions in [def] must be in [regs] *)
  let check r = Sreg.mem r sregs || raise (UnboundRegion r) in
  ignore (option_map (vty_v_all Util.ttrue check) def);
  (* if a type is a model alias, expand everything on the RHS *)
  (* let def = if model then option_map (vty_mod purets) def else def in *)
  { vts_pure  = purets;
    vts_args  = args;
    vts_regs  = regs;
    vts_def   = def; }

(* symbol-wise map/fold *)

(*
let rec vty_s_map fn vty = match vty.vty_node with
  | Vtyvar _ -> ty
  | Vtyapp (f, tl) -> vty_app (fn f) (List.map (vty_s_map fn) tl)

let rec ty_s_fold fn acc ty = match ty.ty_node with
  | Tyvar _ -> acc
  | Tyapp (f, tl) -> List.fold_left (ty_s_fold fn) (fn acc f) tl

let ty_s_all pr ty =
  try ty_s_fold (all_fn pr) true ty with FoldSkip -> false

let ty_s_any pr ty =
  try ty_s_fold (any_fn pr) false ty with FoldSkip -> true

(* type matching *)

let rec ty_inst s ty = match ty.ty_node with
  | Tyvar n -> Mrv.find_default n ty s
  | _ -> ty_map (ty_inst s) ty

let rec ty_match s ty1 ty2 =
  let set = function
    | None -> Some ty2
    | Some ty1 as r when ty_equal ty1 ty2 -> r
    | _ -> raise Exit
  in
  match ty1.ty_node, ty2.ty_node with
    | Tyapp (f1,l1), Tyapp (f2,l2) when ts_equal f1 f2 ->
        List.fold_left2 ty_match s l1 l2
    | Tyvar n1, _ -> Mrv.change n1 set s
    | _ -> raise Exit

exception TypeMismatch of ty * ty

let ty_match s ty1 ty2 =
  try ty_match s ty1 ty2
  with Exit -> raise (TypeMismatch (ty_inst s ty1, ty2))

(* built-in symbols *)

let ts_int  = create_tysymbol (id_fresh "int")  [] None
let ts_real = create_tysymbol (id_fresh "real") [] None

let ty_int  = ty_app ts_int  []
let ty_real = ty_app ts_real []

let ts_func =
  let rv_a = create_rvsymbol (id_fresh "a") in
  let rv_b = create_rvsymbol (id_fresh "b") in
  create_tysymbol (id_fresh "func") [rv_a;rv_b] None

let ts_pred =
  let rv_a = create_rvsymbol (id_fresh "a") in
  create_tysymbol (id_fresh "pred") [rv_a] None

let ty_func ty_a ty_b = ty_app ts_func [ty_a;ty_b]
let ty_pred ty_a = ty_app ts_pred [ty_a]

let ts_tuple_ids = Hid.create 17

let ts_tuple = Util.memo_int 17 (fun n ->
  let vl = ref [] in
  for i = 1 to n do vl := create_rvsymbol (id_fresh "a") :: !vl done;
  let ts = create_tysymbol (id_fresh ("tuple" ^ string_of_int n)) !vl None in
  Hid.add ts_tuple_ids ts.ts_name n;
  ts)

let ty_tuple tyl = ty_app (ts_tuple (List.length tyl)) tyl

let is_ts_tuple ts = ts_equal ts (ts_tuple (List.length ts.ts_args))

let is_ts_tuple_id id =
  try Some (Hid.find ts_tuple_ids id) with Not_found -> None

(** {2 Operations on [ty option]} *)

exception UnexpectedProp

let oty_type = function Some ty -> ty | None -> raise UnexpectedProp

let oty_equal = Util.option_eq ty_equal
let oty_hash = Util.option_apply 1 ty_hash

let oty_match m o1 o2 = match o1,o2 with
  | Some ty1, Some ty2 -> ty_match m ty1 ty2
  | None, None -> m
  | _ -> raise UnexpectedProp

let oty_inst m = Util.option_map (ty_inst m)
let oty_freevars = Util.option_fold ty_freevars
let oty_cons = Util.option_fold (fun tl t -> t::tl)

let ty_equal_check ty1 ty2 =
  if not (ty_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))
*)
