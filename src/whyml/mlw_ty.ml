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

(** region variables *)

type rvsymbol = {
  rv_name : ident;
}

module Rvar = WeakStructMake (struct
  type t = rvsymbol
  let tag rv = rv.rv_name.id_tag
end)

module Srv = Rvar.S
module Mrv = Rvar.M
module Hrv = Rvar.H
module Wrv = Rvar.W

let rv_equal : rvsymbol -> rvsymbol -> bool = (==)

let rv_hash rv = id_hash rv.rv_name

let create_rvsymbol n = { rv_name = id_register n }

(** subregion projections *)

type srsymbol = {
  srs_name : ident;
}

let srs_equal : srsymbol -> srsymbol -> bool = (==)

let srs_hash srs = id_hash srs.srs_name

let create_srsymbol n = { srs_name = id_register n }

(** regions *)

type region = {
  reg_node : reg_node;
  reg_tag  : Hashweak.tag;
}

and reg_node =
  | Rvar of rvsymbol
  | Rsub of srsymbol * region

let reg_equal : region -> region -> bool = (==)

let reg_hash r = Hashweak.tag_hash r.reg_tag

module Hregion = Hashcons.Make (struct
  type t = region

  let equal r1 r2 = match r1.reg_node, r2.reg_node with
    | Rvar n1, Rvar n2 -> rv_equal n1 n2
    | Rsub (s1,r1), Rsub (s2,r2) ->
        srs_equal s1 s2 && reg_equal r1 r2
    | _ -> false

  let hash r = match r.reg_node with
    | Rvar v -> rv_hash v
    | Rsub (s,r) -> Hashcons.combine (srs_hash s) (reg_hash r)

  let tag n r = { r with reg_tag = Hashweak.create_tag n }
end)

module Reg = WeakStructMake (struct
  type t = region
  let tag r = r.reg_tag
end)

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

let mk_reg n = {
  reg_node = n;
  reg_tag  = Hashweak.dummy_tag;
}

let reg_var n = Hregion.hashcons (mk_reg (Rvar n))
let reg_sub s r = Hregion.hashcons (mk_reg (Rsub (s,r)))

let rec reg_getrv r = match r.reg_node with
  | Rvar v -> v
  | Rsub (_,r) -> reg_getrv r

let rec reg_v_map fn r = match r.reg_node with
  | Rvar v -> fn v
  | Rsub (s,r) -> reg_sub s (reg_v_map fn r)

let reg_full_inst m r = reg_v_map (fun v -> Mrv.find v m) r

(** value types (w/o effects) *)

type vtysymbol = {
  vts_pure  : tysymbol;
  vts_args  : tvsymbol list;
  vts_regs  : rvsymbol list;
  vts_def   : vty option;
  vts_model : bool;
}

and vty = {
  vty_node : vty_node;
  vty_tag  : Hashweak.tag;
}

and vty_node =
  | Vtyvar of tvsymbol
  | Vtypur of tysymbol * vty list
  | Vtyapp of vtysymbol * vty list * region list

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
    | Vtyvar n1, Vtyvar n2 -> tv_equal n1 n2
    | Vtypur (s1,l1), Vtypur (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 vty_equal l1 l2
    | Vtyapp (s1,l1,r1), Vtyapp (s2,l2,r2) ->
        vts_equal s1 s2 && List.for_all2 vty_equal l1 l2
          && List.for_all2 reg_equal r1 r2
    | _ -> false

  let hash vty = match vty.vty_node with
    | Vtyvar v -> tv_hash v
    | Vtypur (s,tl) -> Hashcons.combine_list vty_hash (ts_hash s) tl
    | Vtyapp (s,tl,rl) ->
        Hashcons.combine_list reg_hash
          (Hashcons.combine_list vty_hash (vts_hash s) tl) rl

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

(* generic traversal functions *)

let vty_map fn vty = match vty.vty_node with
  | Vtyvar _ -> vty
  | Vtypur (f,tl) -> vty_pur f (List.map fn tl)
  | Vtyapp (f,tl,rl) -> vty_app f (List.map fn tl) rl

let vty_fold fn acc vty = match vty.vty_node with
  | Vtyvar _ -> acc
  | Vtypur (_,tl)
  | Vtyapp (_,tl,_) -> List.fold_left fn acc tl

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

let rec vty_v_fold fnv fnr acc vty = match vty.vty_node with
  | Vtyvar v ->
      fnv acc v
  | Vtypur (_,tl) ->
      List.fold_left (vty_v_fold fnv fnr) acc tl
  | Vtyapp (_,tl,rl) ->
      List.fold_left (vty_v_fold fnv fnr) (List.fold_left fnr acc rl) tl

let vty_v_all prv prr vty =
  try vty_v_fold (all_fn prv) (all_fn prr) true vty with FoldSkip -> false

let vty_v_any prv prr vty =
  try vty_v_fold (any_fn prv) (any_fn prr) false vty with FoldSkip -> true

let vty_full_inst mv mr vty =
  vty_v_map (fun v -> Mtv.find v mv) (reg_full_inst mr) vty

let vty_freevars s vty = vty_v_fold (fun s v -> Stv.add v s) Util.const s vty

let vty_closed vty = vty_v_all Util.ffalse Util.ttrue vty
let vty_pure vty = vty_v_all Util.ttrue Util.ffalse vty

(* smart constructors *)

exception BadVtyArity of vtysymbol * int * int
exception BadRegArity of vtysymbol * int * int

exception DuplicateRegVar of rvsymbol
exception UnboundRegVar of rvsymbol
exception InvalidRegion of region

let rec ty_of_vty vty = match vty.vty_node with
  | Vtyvar v -> ty_var v
  | Vtypur (s,tl) -> ty_app s (List.map ty_of_vty tl)
  | Vtyapp (s,tl,_) -> ty_app s.vts_pure (List.map ty_of_vty tl)

let rec vty_of_ty ty = match ty.ty_node with
  | Tyvar v -> vty_var v
  | Tyapp (s,tl) -> vty_pur s (List.map vty_of_ty tl)

let rec vty_app_real s tl rl model =
  let tll = List.length tl in
  let rll = List.length rl in
  let stl = List.length s.vts_args in
  let srl = List.length s.vts_regs in
  if tll <> stl then raise (BadVtyArity (s,stl,tll));
  if rll <> srl then raise (BadRegArity (s,srl,rll));
  let expand = not s.vts_model || model in
  let subexp = not s.vts_model && model in
  match s.vts_def with
  | Some vty when expand ->
      let add m v t = Mtv.add v t m in
      let mv = List.fold_left2 add Mtv.empty s.vts_args tl in
      let add m v r = Mrv.add v r m in
      let mr = List.fold_left2 add Mrv.empty s.vts_regs rl in
      (* if s is a model alias, vty is already expanded *)
      let vty = if subexp then vty_model vty else vty in
      vty_full_inst mv mr vty
  | None when expand && rll = 0 ->
      (* if a pure non-model vts is an alias, the RHS can contain
         pure model alias types, so we cannot replace vts with ts *)
      (* also, model types should never be replaced with pure types *)
      vty_pur s.vts_pure tl
  | _ ->
      vty_app s tl rl

and vty_model vty = match vty.vty_node with
  | Vtyvar _ -> vty
  | Vtypur (s,tl) -> vty_pur s (List.map vty_model tl)
  | Vtyapp (s,tl,rl) -> vty_app_real s (List.map vty_model tl) rl true

let vty_pur s tl = match s.ts_def with
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let m = List.fold_left2 add Mtv.empty s.ts_args tl in
      vty_full_inst m Mrv.empty (vty_of_ty ty)
  | None ->
      vty_pur s tl

let vty_app s tl rl = vty_app_real s tl rl false
let vty_app_model s tl rl = vty_app_real s tl rl true

let create_vtysymbol name args regs def model =
  let puredef = option_map ty_of_vty def in
  let purets = create_tysymbol name args puredef in
  let add s v = Srv.add_new v (DuplicateRegVar v) s in
  let s = List.fold_left add Srv.empty regs in
  let check r = match r.reg_node with
    | Rvar v -> Srv.mem v s || raise (UnboundRegVar v)
    | _ -> raise (InvalidRegion r) in
  ignore (option_map (vty_v_all Util.ttrue check) def);
  (* if a type is a model alias, expand everything on the RHS *)
  let def = if model then option_map vty_model def else def in
  { vts_pure  = purets;
    vts_args  = args;
    vts_regs  = regs;
    vts_def   = def;
    vts_model = model; }

(*
(* symbol-wise map/fold *)

let rec ty_s_map fn ty = match ty.ty_node with
  | Tyvar _ -> ty
  | Tyapp (f, tl) -> ty_app (fn f) (List.map (ty_s_map fn) tl)

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
