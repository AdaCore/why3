(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Util
open Ident

(** Types *)

type tvsymbol = {
  tv_name : ident;
}

module Tvar = StructMake (struct
  type t = tvsymbol
  let tag tv = tv.tv_name.id_tag
end)

module Stv = Tvar.S
module Mtv = Tvar.M
module Htv = Tvar.H

let tv_equal = (==)

let create_tvsymbol n = { tv_name = id_register n }

(* type symbols and types *)

type tysymbol = {
  ts_name : ident;
  ts_args : tvsymbol list;
  ts_def  : ty option;
}

and ty = {
  ty_node : ty_node;
  ty_tag : int;
}

and ty_node =
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

module Tsym = StructMake (struct
  type t = tysymbol
  let tag ts = ts.ts_name.id_tag
end)

module Sts = Tsym.S
module Mts = Tsym.M
module Hts = Tsym.H
module Wts = Tsym.W

let ts_equal = (==)
let ty_equal = (==)

let mk_ts name args def = {
  ts_name = name;
  ts_args = args;
  ts_def  = def;
}

let create_tysymbol name args def = mk_ts (id_register name) args def

module Hsty = Hashcons.Make (struct
  type t = ty

  let equal ty1 ty2 = match ty1.ty_node, ty2.ty_node with
    | Tyvar n1, Tyvar n2 -> tv_equal n1 n2
    | Tyapp (s1,l1), Tyapp (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 ty_equal l1 l2
    | _ -> false

  let hash_ty ty = ty.ty_tag

  let hash ty = match ty.ty_node with
    | Tyvar v -> v.tv_name.id_tag
    | Tyapp (s,tl) -> Hashcons.combine_list hash_ty s.ts_name.id_tag tl

  let tag n ty = { ty with ty_tag = n }
end)

module Tty = struct
  type t = ty
  let tag ty = ty.ty_tag
end

module Ty = StructMake (Tty)

module Sty = Ty.S
module Mty = Ty.M
module Hty = Ty.H
module Wty = Ty.W

let mk_ty n = { ty_node = n; ty_tag = -1 }
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
  try ty_fold (all_fn pr) true ty with FoldSkip -> false

let ty_any pr ty =
  try ty_fold (any_fn pr) false ty with FoldSkip -> true

(* smart constructors *)

exception BadTypeArity of tysymbol * int * int
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVars of Stv.t

let rec tv_known s acc ty = match ty.ty_node with
  | Tyvar n when not (Stv.mem n s) -> Stv.add n acc
  | _ -> ty_fold (tv_known s) acc ty

let create_tysymbol name args def =
  let add s v =
    if Stv.mem v s then raise (DuplicateTypeVar v);
    Stv.add v s
  in
  let s = List.fold_left add Stv.empty args in
  begin match def with
    | Some ty ->
        let ts = tv_known s Stv.empty ty in
        if not (Stv.is_empty ts) then raise (UnboundTypeVars ts)
    | _ -> ()
  end;
  create_tysymbol name args def

let rec tv_inst m ty = match ty.ty_node with
  | Tyvar n -> Mtv.find n m
  | _ -> ty_map (tv_inst m) ty

let ty_app s tl =
  let tll = List.length tl in
  let stl = List.length s.ts_args in
  if tll <> stl then raise (BadTypeArity (s,stl,tll));
  match s.ts_def with
    | Some ty ->
        let add m v t = Mtv.add v t m in
        tv_inst (List.fold_left2 add Mtv.empty s.ts_args tl) ty
    | _ ->
        ty_app s tl

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
  | Tyvar n -> (try Mtv.find n s with Not_found -> ty)
  | _ -> ty_map (ty_inst s) ty

let rec ty_match s ty1 ty2 =
  if ty_equal ty1 ty2 then s
  else match ty1.ty_node, ty2.ty_node with
    | Tyvar n1, _ ->
        (try if ty_equal (Mtv.find n1 s) ty2
              then s else raise Exit
         with Not_found -> Mtv.add n1 ty2 s)
    | Tyapp (f1, l1), Tyapp (f2, l2) when ts_equal f1 f2 ->
        List.fold_left2 ty_match s l1 l2
    | _ ->
        raise Exit

exception TypeMismatch of ty * ty

let ty_match s ty1 ty2 =
  try ty_match s ty1 ty2
  with Exit -> raise (TypeMismatch (ty_inst s ty1, ty2))

(* built-in symbols *)

let ts_int  = create_tysymbol (id_fresh "int")  [] None
let ts_real = create_tysymbol (id_fresh "real") [] None

let ty_int  = ty_app ts_int  []
let ty_real = ty_app ts_real []

let ts_tuple n = 
  let vl = ref [] in
  for i = 1 to n do vl := create_tvsymbol (id_fresh "a") :: !vl done;
  create_tysymbol (id_fresh ("tuple" ^ string_of_int n)) !vl None

let ts_tuple = Util.memo ts_tuple

let ty_tuple tyl =
  ty_app (ts_tuple (List.length tyl)) tyl

let is_ts_tuple ts = ts == ts_tuple (List.length ts.ts_args)


open Format
let print_tv fmt tv = pp_print_string fmt tv.tv_name.id_string
let print_ts fmt ts = pp_print_string fmt ts.ts_name.id_string

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, [t]) -> fprintf fmt "%a@ %a" print_ty t print_ts ts
  | Tyapp (ts, l) -> fprintf fmt "(%a)@ %a"
      (Pp.print_list Pp.comma print_ty) l print_ts ts


let () = Exn_printer.register
  (fun fmt exn -> match exn with
    | TypeMismatch (t1,t2) ->
        Format.fprintf fmt "Type mismatch between %a and %a" 
          print_ty t1 print_ty t2
    | BadTypeArity(ts, ts_arg, app_arg) ->
      Format.fprintf fmt 
        "Bad type arity type symbol %a is applied \
         with %i arguments instead of %i"
        print_ts ts ts_arg app_arg
    | _ -> raise exn)
