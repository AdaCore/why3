(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident

(** Types *)

type tvsymbol = {
  tv_name : ident;
}

module Tvar = Stdlib.MakeMSHW (struct
  type t = tvsymbol
  let tag tv = tv.tv_name.id_tag
end)

module Stv = Tvar.S
module Mtv = Tvar.M
module Htv = Tvar.H

let tv_equal : tvsymbol -> tvsymbol -> bool = (==)
let tv_hash tv = id_hash tv.tv_name
let tv_compare tv1 tv2 = id_compare tv1.tv_name tv2.tv_name

let create_tvsymbol n = { tv_name = id_register n }

let tv_of_string =
  let hs = Hstr.create 17 in fun s ->
  try Hstr.find hs s with Not_found ->
  let tv = create_tvsymbol (id_fresh s) in
  Hstr.add hs s tv;
  tv

(* type symbols and types *)

type tysymbol = {
  ts_name : ident;
  ts_args : tvsymbol list;
  ts_def  : ty option;
}

and ty = {
  ty_node : ty_node;
  ty_tag  : Weakhtbl.tag;
}

and ty_node =
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

module Tsym = Stdlib.MakeMSHW (struct
  type t = tysymbol
  let tag ts = ts.ts_name.id_tag
end)

module Sts = Tsym.S
module Mts = Tsym.M
module Hts = Tsym.H
module Wts = Tsym.W

let ts_equal : tysymbol -> tysymbol -> bool = (==)
let ty_equal : ty       -> ty       -> bool = (==)

let ts_hash ts = id_hash ts.ts_name
let ty_hash ty = Weakhtbl.tag_hash ty.ty_tag

let ts_compare ts1 ts2 = id_compare ts1.ts_name ts2.ts_name
let ty_compare ty1 ty2 = Pervasives.compare (ty_hash ty1) (ty_hash ty2)

let mk_ts name args def = {
  ts_name = id_register name;
  ts_args = args;
  ts_def  = def;
}

module Hsty = Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 = match ty1.ty_node, ty2.ty_node with
    | Tyvar n1, Tyvar n2 -> tv_equal n1 n2
    | Tyapp (s1,l1), Tyapp (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 ty_equal l1 l2
    | _ -> false

  let hash ty = match ty.ty_node with
    | Tyvar v -> tv_hash v
    | Tyapp (s,tl) -> Hashcons.combine_list ty_hash (ts_hash s) tl

  let tag n ty = { ty with ty_tag = Weakhtbl.create_tag n }
end)

module Ty = MakeMSHW (struct
  type t = ty
  let tag ty = ty.ty_tag
end)

module Sty = Ty.S
module Mty = Ty.M
module Hty = Ty.H
module Wty = Ty.W

let mk_ty n = {
  ty_node = n;
  ty_tag  = Weakhtbl.dummy_tag;
}

let ty_var n = Hsty.hashcons (mk_ty (Tyvar n))
let ty_app s tl = Hsty.hashcons (mk_ty (Tyapp (s, tl)))

(* generic traversal functions *)

let ty_map fn ty = match ty.ty_node with
  | Tyvar _ -> ty
  | Tyapp (f, tl) -> ty_app f (List.map fn tl)

let ty_fold fn acc ty = match ty.ty_node with
  | Tyvar _ -> acc
  | Tyapp (_, tl) -> List.fold_left fn acc tl

let ty_all pr ty =
  try ty_fold (Util.all_fn pr) true ty with Util.FoldSkip -> false

let ty_any pr ty =
  try ty_fold (Util.any_fn pr) false ty with Util.FoldSkip -> true

(* traversal functions on type variables *)

let rec ty_v_map fn ty = match ty.ty_node with
  | Tyvar v -> fn v
  | Tyapp (f, tl) -> ty_app f (List.map (ty_v_map fn) tl)

let rec ty_v_fold fn acc ty = match ty.ty_node with
  | Tyvar v -> fn acc v
  | Tyapp (_, tl) -> List.fold_left (ty_v_fold fn) acc tl

let ty_v_all pr ty =
  try ty_v_fold (Util.all_fn pr) true ty with Util.FoldSkip -> false

let ty_v_any pr ty =
  try ty_v_fold (Util.any_fn pr) false ty with Util.FoldSkip -> true

let ty_full_inst m ty = ty_v_map (fun v -> Mtv.find v m) ty
let ty_freevars s ty = ty_v_fold (fun s v -> Stv.add v s) s ty
let ty_closed ty = ty_v_all Util.ffalse ty

(* smart constructors *)

exception BadTypeArity of tysymbol * int
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVar of tvsymbol

let create_tysymbol name args def =
  let add s v = Stv.add_new (DuplicateTypeVar v) v s in
  let s = List.fold_left add Stv.empty args in
  let check v = Stv.mem v s || raise (UnboundTypeVar v) in
  ignore (Opt.map (ty_v_all check) def);
  mk_ts name args def

let ty_app s tl = match s.ts_def with
  | Some ty ->
      let mv = try List.fold_right2 Mtv.add s.ts_args tl Mtv.empty with
        | Invalid_argument _ -> raise (BadTypeArity (s, List.length tl)) in
      ty_full_inst mv ty
  | None ->
      if List.length s.ts_args <> List.length tl then
        raise (BadTypeArity (s, List.length tl));
      ty_app s tl

(* symbol-wise map/fold *)

let rec ty_s_map fn ty = match ty.ty_node with
  | Tyvar _ -> ty
  | Tyapp (f, tl) -> ty_app (fn f) (List.map (ty_s_map fn) tl)

let rec ty_s_fold fn acc ty = match ty.ty_node with
  | Tyvar _ -> acc
  | Tyapp (f, tl) -> List.fold_left (ty_s_fold fn) (fn acc f) tl

let ty_s_all pr ty =
  try ty_s_fold (Util.all_fn pr) true ty with Util.FoldSkip -> false

let ty_s_any pr ty =
  try ty_s_fold (Util.any_fn pr) false ty with Util.FoldSkip -> true

(* type matching *)

let rec ty_inst s ty = match ty.ty_node with
  | Tyvar n -> Mtv.find_def ty n s
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
    | Tyvar n1, _ -> Mtv.change set n1 s
    | _ -> raise Exit

exception TypeMismatch of ty * ty

let ty_match s ty1 ty2 =
  try ty_match s ty1 ty2
  with Exit -> raise (TypeMismatch (ty_inst s ty1, ty2))

(* built-in symbols *)

let ts_int  = create_tysymbol (id_fresh "int")  [] None
let ts_real = create_tysymbol (id_fresh "real") [] None
let ts_bool = create_tysymbol (id_fresh "bool") [] None

let ty_int  = ty_app ts_int  []
let ty_real = ty_app ts_real []
let ty_bool = ty_app ts_bool []

let ts_func =
  let tv_a = create_tvsymbol (id_fresh "a") in
  let tv_b = create_tvsymbol (id_fresh "b") in
  create_tysymbol (id_fresh "func") [tv_a;tv_b] None

let ty_func ty_a ty_b = ty_app ts_func [ty_a;ty_b]

let ts_pred =
  let tv_a = create_tvsymbol (id_fresh "a") in
  let def = Some (ty_func (ty_var tv_a) ty_bool) in
  create_tysymbol (id_fresh "pred") [tv_a] def

let ty_pred ty_a = ty_app ts_pred [ty_a]

let ts_tuple_ids = Hid.create 17

let ts_tuple = Hint.memo 17 (fun n ->
  let vl = ref [] in
  for _i = 1 to n do vl := create_tvsymbol (id_fresh "a") :: !vl done;
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

let oty_equal = Opt.equal ty_equal
let oty_hash = Opt.fold (fun _ -> ty_hash) 1

let oty_compare o1 o2 = Opt.compare ty_compare o1 o2

let oty_match m o1 o2 = match o1,o2 with
  | Some ty1, Some ty2 -> ty_match m ty1 ty2
  | None, None -> m
  | _ -> raise UnexpectedProp

let oty_inst m = Opt.map (ty_inst m)
let oty_freevars = Opt.fold ty_freevars
let oty_cons = Opt.fold (fun tl t -> t::tl)

let ty_equal_check ty1 ty2 =
  if not (ty_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))

