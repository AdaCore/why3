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
open Ty

(** Variable symbols *)

type vsymbol = {
  vs_name : ident;
  vs_ty   : ty;
}

module Vsym = WeakStructMake (struct
  type t = vsymbol
  let tag vs = vs.vs_name.id_tag
end)

module Svs = Vsym.S
module Mvs = Vsym.M
module Hvs = Vsym.H

let vs_equal = (==)

let vs_hash vs = id_hash vs.vs_name

let create_vsymbol name ty = {
  vs_name = id_register name;
  vs_ty   = ty;
}

let fresh_vsymbol v = create_vsymbol (id_dup v.vs_name) v.vs_ty

(** Function and predicate symbols *)

type lsymbol = {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
}

module Lsym = WeakStructMake (struct
  type t = lsymbol
  let tag ls = ls.ls_name.id_tag
end)

module Sls = Lsym.S
module Mls = Lsym.M
module Hls = Lsym.H
module Wls = Lsym.W

let ls_equal = (==)

let ls_hash ls = id_hash ls.ls_name

let create_lsymbol name args value = {
  ls_name   = id_register name;
  ls_args   = args;
  ls_value  = value;
}

let create_fsymbol nm al vl = create_lsymbol nm al (Some vl)
let create_psymbol nm al    = create_lsymbol nm al (None)

let ls_ty_freevars ls =
  let acc = match ls.ls_value with
    | None -> Stv.empty
    | Some ty -> ty_freevars Stv.empty ty
  in
  List.fold_left ty_freevars acc ls.ls_args

(** Patterns *)

type pattern = {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Por  of pattern * pattern
  | Pas  of pattern * vsymbol

let pat_equal = (==)

let pat_hash p = p.pat_tag

module Hspat = Hashcons.Make (struct
  type t = pattern

  let equal_node p1 p2 = match p1, p2 with
    | Pwild, Pwild -> true
    | Pvar v1, Pvar v2 -> vs_equal v1 v2
    | Papp (s1, l1), Papp (s2, l2) ->
        ls_equal s1 s2 && List.for_all2 pat_equal l1 l2
    | Por (p1, q1), Por (p2, q2) ->
        pat_equal p1 p2 && pat_equal q1 q2
    | Pas (p1, n1), Pas (p2, n2) ->
        pat_equal p1 p2 && vs_equal n1 n2
    | _ -> false

  let equal p1 p2 =
    equal_node p1.pat_node p2.pat_node && ty_equal p1.pat_ty p2.pat_ty

  let hash_node = function
    | Pwild -> 0
    | Pvar v -> vs_hash v
    | Papp (s, pl) -> Hashcons.combine_list pat_hash (ls_hash s) pl
    | Por (p, q) -> Hashcons.combine (pat_hash p) (pat_hash q)
    | Pas (p, v) -> Hashcons.combine (pat_hash p) (vs_hash v)

  let hash p = Hashcons.combine (hash_node p.pat_node) (ty_hash p.pat_ty)

  let tag n p = { p with pat_tag = n }
end)

module Pat = StructMake (struct
  type t = pattern
  let tag pat = pat.pat_tag
end)

module Spat = Pat.S
module Mpat = Pat.M
module Hpat = Pat.H

(* h-consing constructors for patterns *)

let mk_pattern n vs ty = Hspat.hashcons {
  pat_node = n;
  pat_vars = vs;
  pat_ty   = ty;
  pat_tag  = -1
}

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

let add_no_dup vs s =
  if Svs.mem vs s then raise (DuplicateVar vs) else Svs.add vs s

let pat_wild ty = mk_pattern Pwild Svs.empty ty
let pat_var v   = mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty
let pat_as p v  = mk_pattern (Pas (p,v)) (add_no_dup v p.pat_vars) v.vs_ty

let pat_or p q =
  if Svs.equal p.pat_vars q.pat_vars then
    mk_pattern (Por (p,q)) p.pat_vars p.pat_ty
  else
    let s1, s2 = p.pat_vars, q.pat_vars in
    let vs = Svs.choose (Svs.union (Svs.diff s1 s2) (Svs.diff s2 s1)) in
    raise (UncoveredVar vs)

let pat_app f pl ty =
  let merge s p = Svs.fold add_no_dup s p.pat_vars in
  mk_pattern (Papp (f,pl)) (List.fold_left merge Svs.empty pl) ty

(* generic traversal functions *)

let pat_map fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as (fn p) v
  | Por (p, q) -> pat_or (fn p) (fn q)

let check_ty_equal ty1 ty2 =
  if not (ty_equal ty1 ty2) then raise (TypeMismatch (ty1, ty2))

let protect fn pat =
  let res = fn pat in
  check_ty_equal pat.pat_ty res.pat_ty;
  res

let pat_map fn = pat_map (protect fn)

let pat_fold fn acc pat = match pat.pat_node with
  | Pwild | Pvar _ -> acc
  | Papp (_, pl) -> List.fold_left fn acc pl
  | Pas (p, _) -> fn acc p
  | Por (p, q) -> fn (fn acc p) q

let pat_all pr pat =
  try pat_fold (all_fn pr) true pat with FoldSkip -> false

let pat_any pr pat =
  try pat_fold (any_fn pr) false pat with FoldSkip -> true

(* smart constructors for patterns *)

exception BadArity of lsymbol * int * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol

let pat_app fs pl ty =
  let s = match fs.ls_value with
    | Some vty -> ty_match Mtv.empty vty ty
    | None -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty p = ty_match s ty p.pat_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args pl
    with Invalid_argument _ -> raise (BadArity
      (fs, List.length fs.ls_args, List.length pl)));
  pat_app fs pl ty

let pat_as p v =
  check_ty_equal p.pat_ty v.vs_ty;
  pat_as p v

let pat_or p q =
  check_ty_equal p.pat_ty q.pat_ty;
  pat_or p q

(* symbol-wise map/fold *)

let rec pat_gen_map fnT fnV fnL pat =
  let fn p = pat_gen_map fnT fnV fnL p in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (fnV v ty)
    | Papp (s, pl) -> pat_app (fnL s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (fnV v ty)
    | Por (p, q) -> pat_or (fn p) (fn q)

let rec pat_gen_fold fnT fnV fnL acc pat =
  let fn acc p = pat_gen_fold fnT fnV fnL acc p in
  let acc = fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild -> acc
    | Pvar v -> fnV acc v
    | Papp (s, pl) -> List.fold_left fn (fnL acc s) pl
    | Por (p, q) -> fn (fn acc p) q
    | Pas (p, v) -> fn (fnV acc v) p

(** Terms and formulas *)

type quant =
  | Fforall
  | Fexists

type binop =
  | Fand
  | For
  | Fimplies
  | Fiff

type real_constant =
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of string
  | ConstReal of real_constant

type term = {
  t_node : term_node;
  t_label : label list;
  t_ty : ty;
  t_tag : int;
}

and fmla = {
  f_node : fmla_node;
  f_label : label list;
  f_tag : int;
}

and term_node =
  | Tbvar of int
  | Tvar of vsymbol
  | Tconst of constant
  | Tapp of lsymbol * term list
  | Tif of fmla * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of fmla_bound

and fmla_node =
  | Fapp of lsymbol * term list
  | Fquant of quant * fmla_quant
  | Fbinop of binop * fmla * fmla
  | Fnot of fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * fmla_bound
  | Fcase of term * fmla_branch list

and term_bound  = vsymbol * bind_info * term
and fmla_bound  = vsymbol * bind_info * fmla

and term_branch = pattern * bind_info * term
and fmla_branch = pattern * bind_info * fmla

and fmla_quant  = vsymbol list * bind_info * trigger list * fmla

and bind_info = {
  bv_bound : int;         (* properly bound and inst-deferred indices *)
  bv_open  : Sint.t;      (* externally visible indices *)
  bv_defer : term Mint.t  (* deferred instantiation *)
}

and trigger = expr list

and expr =
  | Term of term
  | Fmla of fmla

(* term and fmla equality *)

let t_equal = (==)
let f_equal = (==)

let t_hash t = t.t_tag
let f_hash f = f.f_tag

(* expr and trigger equality *)

let e_equal e1 e2 = match e1, e2 with
  | Term t1, Term t2 -> t_equal t1 t2
  | Fmla f1, Fmla f2 -> f_equal f1 f2
  | _ -> false

let tr_equal = list_all2 (list_all2 e_equal)

(* expr and trigger traversal *)

let e_map fnT fnF = function Term t -> Term (fnT t) | Fmla f -> Fmla (fnF f)
let e_fold fnT fnF acc = function Term t -> fnT acc t | Fmla f -> fnF acc f
let e_apply fnT fnF = function Term t -> fnT t | Fmla f -> fnF f

let e_map_fold fnT fnF acc = function
  | Term t -> let acc, t = fnT acc t in acc, Term t
  | Fmla f -> let acc, f = fnF acc f in acc, Fmla f

let tr_map fnT fnF = List.map (List.map (e_map fnT fnF))
let tr_fold fnT fnF = List.fold_left (List.fold_left (e_fold fnT fnF))

let tr_map_fold fnT fnF =
  Util.map_fold_left (Util.map_fold_left (e_map_fold fnT fnF))

(* bind_info equality, hash, and traversal *)

let bnd_equal b1 b2 =
  b1.bv_bound = b2.bv_bound && Mint.equal t_equal b1.bv_defer b2.bv_defer

let bnd_hash bv =
  Mint.fold (fun i t a -> Hashcons.combine2 i (t_hash t) a) bv.bv_defer

let bnd_map fn bv = { bv with bv_defer = Mint.map fn bv.bv_defer }
let bnd_fold fn acc bv = Mint.fold (fun _ t a -> fn a t) bv.bv_defer acc

let bnd_map_fold fn acc bv =
  let acc,s = Mint.fold
    (fun i t (a,b) -> let a,t = fn a t in a, Mint.add i t b)
    bv.bv_defer (acc, Mint.empty)
  in
  acc, { bv with bv_defer = s }

(* hash-consing for terms and formulas *)

module Hsterm = Hashcons.Make (struct

  type t = term

  let t_eq_branch (p1,b1,t1) (p2,b2,t2) =
    pat_equal p1 p2 && bnd_equal b1 b2 && t_equal t1 t2

  let t_eq_bound (v1,b1,t1) (v2,b2,t2) =
    vs_equal v1 v2 && bnd_equal b1 b2 && t_equal t1 t2

  let f_eq_bound (v1,b1,f1) (v2,b2,f2) =
    vs_equal v1 v2 && bnd_equal b1 b2 && f_equal f1 f2

  let t_equal_node t1 t2 = match t1,t2 with
    | Tbvar x1, Tbvar x2 -> x1 = x2
    | Tvar v1, Tvar v2 -> vs_equal v1 v2
    | Tconst c1, Tconst c2 -> c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_equal l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        f_equal f1 f2 && t_equal t1 t2 && t_equal e1 e2
    | Tlet (t1,b1), Tlet (t2,b2) ->
        t_equal t1 t2 && t_eq_bound b1 b2
    | Tcase (t1,bl1), Tcase (t2,bl2) ->
        t_equal t1 t2 && list_all2 t_eq_branch bl1 bl2
    | Teps f1, Teps f2 -> f_eq_bound f1 f2
    | _ -> false

  let equal t1 t2 =
    t_equal t1.t_ty t2.t_ty &&
    t_equal_node t1.t_node t2.t_node &&
    list_all2 (=) t1.t_label t2.t_label

  let t_hash_branch (p,b,t) =
    Hashcons.combine (pat_hash p) (bnd_hash b (t_hash t))

  let t_hash_bound (v,b,t) =
    Hashcons.combine (vs_hash v) (bnd_hash b (t_hash t))

  let f_hash_bound (v,b,f) =
    Hashcons.combine (vs_hash v) (bnd_hash b (f_hash f))

  let t_hash_node = function
    | Tbvar n -> n
    | Tvar v -> vs_hash v
    | Tconst c -> Hashtbl.hash c
    | Tapp (f,tl) -> Hashcons.combine_list t_hash (ls_hash f) tl
    | Tif (f,t,e) -> Hashcons.combine2 (f_hash f) (t_hash t) (t_hash e)
    | Tlet (t,bt) -> Hashcons.combine (t_hash t) (t_hash_bound bt)
    | Tcase (t,bl) -> Hashcons.combine_list t_hash_branch (t_hash t) bl
    | Teps f -> f_hash_bound f

  let hash t =
    Hashcons.combine (t_hash_node t.t_node)
      (Hashcons.combine_list Hashtbl.hash (ty_hash t.t_ty) t.t_label)

  let tag n t = { t with t_tag = n }

end)

module Term = StructMake (struct
  type t = term
  let tag term = term.t_tag
end)

module Sterm = Term.S
module Mterm = Term.M
module Hterm = Term.H

module Hsfmla = Hashcons.Make (struct

  type t = fmla

  let f_eq_branch (p1,b1,f1) (p2,b2,f2) =
    pat_equal p1 p2 && bnd_equal b1 b2 && f_equal f1 f2

  let f_eq_bound (v1,b1,f1) (v2,b2,f2) =
    vs_equal v1 v2 && bnd_equal b1 b2 && f_equal f1 f2

  let f_eq_quant (vl1,b1,tl1,f1) (vl2,b2,tl2,f2) =
    f_equal f1 f2 && list_all2 vs_equal vl1 vl2 &&
    bnd_equal b1 b2 && tr_equal tl1 tl2

  let f_equal_node f1 f2 = match f1,f2 with
    | Fapp (s1,l1), Fapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_equal l1 l2
    | Fquant (q1,b1), Fquant (q2,b2) ->
        q1 = q2 && f_eq_quant b1 b2
    | Fbinop (op1,f1,g1), Fbinop (op2,f2,g2) ->
        op1 = op2 && f_equal f1 f2 && f_equal g1 g2
    | Fnot f1, Fnot f2 -> f_equal f1 f2
    | Ftrue, Ftrue | Ffalse, Ffalse -> true
    | Fif (f1,g1,h1), Fif (f2,g2,h2) ->
        f_equal f1 f2 && f_equal g1 g2 && f_equal h1 h2
    | Flet (t1,b1), Flet (t2,b2) ->
        t_equal t1 t2 && f_eq_bound b1 b2
    | Fcase (t1,bl1), Fcase (t2,bl2) ->
        t_equal t1 t2 && list_all2 f_eq_branch bl1 bl2
    | _ -> false

  let equal f1 f2 =
    f_equal_node f1.f_node f2.f_node &&
    list_all2 (=) f1.f_label f2.f_label

  let f_hash_branch (p,b,f) =
    Hashcons.combine (pat_hash p) (bnd_hash b (f_hash f))

  let f_hash_bound (v,b,f) =
    Hashcons.combine (vs_hash v) (bnd_hash b (f_hash f))

  let e_hash = function Term t -> t_hash t | Fmla f -> f_hash f

  let f_hash_quant (vl,b,tl,f) =
    let h = bnd_hash b (f_hash f) in
    let h = Hashcons.combine_list vs_hash h vl in
    List.fold_left (Hashcons.combine_list e_hash) h tl

  let f_hash_node = function
    | Fapp (p,tl) -> Hashcons.combine_list t_hash (ls_hash p) tl
    | Fquant (q,bf) -> Hashcons.combine (Hashtbl.hash q) (f_hash_quant bf)
    | Fbinop (op,f1,f2) ->
        Hashcons.combine2 (Hashtbl.hash op) (f_hash f1) (f_hash f2)
    | Fnot f -> Hashcons.combine 1 (f_hash f)
    | Ftrue -> 0
    | Ffalse -> 1
    | Fif (f1,f2,f3) -> Hashcons.combine2 (f_hash f1) (f_hash f2) (f_hash f3)
    | Flet (t,bf) -> Hashcons.combine (t_hash t) (f_hash_bound bf)
    | Fcase (t,bl) -> Hashcons.combine_list f_hash_branch (t_hash t) bl

  let hash f =
    Hashcons.combine_list Hashtbl.hash (f_hash_node f.f_node) f.f_label

  let tag n f = { f with f_tag = n }

end)

module Fmla = StructMake (struct
  type t = fmla
  let tag fmla = fmla.f_tag
end)

module Sfmla = Fmla.S
module Mfmla = Fmla.M
module Hfmla = Fmla.H

(* hash-consing constructors for terms *)

let mk_term n ty = Hsterm.hashcons {
  t_node = n; t_label = []; t_ty = ty; t_tag = -1 }

let t_bvar n ty     = mk_term (Tbvar n) ty
let t_var v         = mk_term (Tvar v) v.vs_ty
let t_const c ty    = mk_term (Tconst c) ty
let t_int_const s   = mk_term (Tconst (ConstInt s)) Ty.ty_int
let t_real_const r  = mk_term (Tconst (ConstReal r)) Ty.ty_real
let t_app f tl ty   = mk_term (Tapp (f, tl)) ty
let t_if f t1 t2    = mk_term (Tif (f, t1, t2)) t2.t_ty
let t_let t1 bt ty  = mk_term (Tlet (t1, bt)) ty
let t_case t1 bl ty = mk_term (Tcase (t1, bl)) ty
let t_eps bf ty     = mk_term (Teps bf) ty

let t_label     l t = Hsterm.hashcons { t with t_label = l }
let t_label_add l t = Hsterm.hashcons { t with t_label = l :: t.t_label }

let t_label_copy { t_label = l } t =
  if t.t_label = [] && l <> [] then t_label l t else t

(* hash-consing constructors for formulas *)

let mk_fmla n = Hsfmla.hashcons { f_node = n; f_label = []; f_tag = -1 }

let f_app f tl        = mk_fmla (Fapp (f, tl))
let f_quant q qf      = mk_fmla (Fquant (q, qf))
let f_binary op f1 f2 = mk_fmla (Fbinop (op, f1, f2))
let f_not f           = mk_fmla (Fnot f)
let f_true            = mk_fmla (Ftrue)
let f_false           = mk_fmla (Ffalse)
let f_if f1 f2 f3     = mk_fmla (Fif (f1, f2, f3))
let f_let t bf        = mk_fmla (Flet (t, bf))
let f_case t bl       = mk_fmla (Fcase (t, bl))

let f_label     l f = Hsfmla.hashcons { f with f_label = l }
let f_label_add l f = Hsfmla.hashcons { f with f_label = l :: f.f_label }

let f_label_copy { f_label = l } f =
  if f.f_label = [] && l <> [] then f_label l f else f

let f_and     = f_binary Fand
let f_or      = f_binary For
let f_implies = f_binary Fimplies
let f_iff     = f_binary Fiff

(* unsafe map *)

let bound_map fnT fnE (u,b,e) = (u, bnd_map fnT b, fnE e)

let t_map_unsafe fnT fnF t = t_label_copy t (match t.t_node with
  | Tbvar _ | Tvar _ | Tconst _ -> t
  | Tapp (f,tl) -> t_app f (List.map fnT tl) t.t_ty
  | Tif (f,t1,t2) -> t_if (fnF f) (fnT t1) (fnT t2)
  | Tlet (e,b) -> t_let (fnT e) (bound_map fnT fnT b) t.t_ty
  | Tcase (e,bl) -> t_case (fnT e) (List.map (bound_map fnT fnT) bl) t.t_ty
  | Teps b -> t_eps (bound_map fnT fnF b) t.t_ty)

let f_map_unsafe fnT fnF f = f_label_copy f (match f.f_node with
  | Fapp (p,tl) -> f_app p (List.map fnT tl)
  | Fquant (q,(vl,b,tl,f1)) ->
      f_quant q (vl, bnd_map fnT b, tr_map fnT fnF tl, fnF f1)
  | Fbinop (op,f1,f2) -> f_binary op (fnF f1) (fnF f2)
  | Fnot f1 -> f_not (fnF f1)
  | Ftrue | Ffalse -> f
  | Fif (f1,f2,f3) -> f_if (fnF f1) (fnF f2) (fnF f3)
  | Flet (e,b) -> f_let (fnT e) (bound_map fnT fnF b)
  | Fcase (e,bl) -> f_case (fnT e) (List.map (bound_map fnT fnF) bl))

(* unsafe fold *)

let bound_fold fnT fnE acc (_,b,e) = fnE (bnd_fold fnT acc b) e

let t_fold_unsafe fnT fnF acc t = match t.t_node with
  | Tbvar _ | Tvar _ | Tconst _ -> acc
  | Tapp (_,tl) -> List.fold_left fnT acc tl
  | Tif (f,t1,t2) -> fnT (fnT (fnF acc f) t1) t2
  | Tlet (e,b) -> fnT (bound_fold fnT fnT acc b) e
  | Tcase (e,bl) -> List.fold_left (bound_fold fnT fnT) (fnT acc e) bl
  | Teps b -> bound_fold fnT fnF acc b

let f_fold_unsafe fnT fnF acc f = match f.f_node with
  | Fapp (_,tl) -> List.fold_left fnT acc tl
  | Fquant (_,(_,b,tl,f1)) -> fnF (tr_fold fnT fnF (bnd_fold fnT acc b) tl) f1
  | Fbinop (_,f1,f2) -> fnF (fnF acc f1) f2
  | Fnot f1 -> fnF acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1,f2,f3) -> fnF (fnF (fnF acc f1) f2) f3
  | Flet (e,b) -> fnT (bound_fold fnT fnF acc b) e
  | Fcase (e,bl) -> List.fold_left (bound_fold fnT fnF) (fnT acc e) bl

let all_fnT prT _ t = prT t || raise FoldSkip
let all_fnF prF _ f = prF f || raise FoldSkip
let any_fnT prT _ t = prT t && raise FoldSkip
let any_fnF prF _ f = prF f && raise FoldSkip

let t_all_unsafe prT prF t =
  try t_fold_unsafe (all_fnT prT) (all_fnF prF) true t
  with FoldSkip -> false

let f_all_unsafe prT prF f =
  try f_fold_unsafe (all_fnT prT) (all_fnF prF) true f
  with FoldSkip -> false

let t_any_unsafe prT prF t =
  try t_fold_unsafe (any_fnT prT) (any_fnF prF) false t
  with FoldSkip -> true

let f_any_unsafe prT prF f =
  try f_fold_unsafe (any_fnT prT) (any_fnF prF) false f
  with FoldSkip -> true

(* unsafe map_fold *)

let bound_map_fold fnT fnE acc (u,b,e) =
  let acc, b = bnd_map_fold fnT acc b in
  let acc, e = fnE acc e in
  acc, (u,b,e)

let t_map_fold_unsafe fnT fnF acc t = match t.t_node with
  | Tbvar _ | Tvar _ | Tconst _ ->
      acc, t
  | Tapp (f,tl) ->
      let acc,tl = map_fold_left fnT acc tl in
      acc, t_label_copy t (t_app f tl t.t_ty)
  | Tif (f,t1,t2) ->
      let acc, f  = fnF acc f in
      let acc, t1 = fnT acc t1 in
      let acc, t2 = fnT acc t2 in
      acc, t_label_copy t (t_if f t1 t2)
  | Tlet (e,b) ->
      let acc, e = fnT acc e in
      let acc, b = bound_map_fold fnT fnT acc b in
      acc, t_label_copy t (t_let e b t.t_ty)
  | Tcase (e,bl) ->
      let acc, e = fnT acc e in
      let acc, bl = map_fold_left (bound_map_fold fnT fnT) acc bl in
      acc, t_label_copy t (t_case e bl t.t_ty)
  | Teps b ->
      let acc, b = bound_map_fold fnT fnF acc b in
      acc, t_label_copy t (t_eps b t.t_ty)

let f_map_fold_unsafe fnT fnF acc f = match f.f_node with
  | Fapp (p,tl) ->
      let acc,tl = map_fold_left fnT acc tl in
      acc, f_label_copy f (f_app p tl)
  | Fquant (q,(vl,b,tl,f1)) ->
      let acc, b = bnd_map_fold fnT acc b in
      let acc, tl = tr_map_fold fnT fnF acc tl in
      let acc, f1 = fnF acc f1 in
      acc, f_label_copy f (f_quant q (vl,b,tl,f1))
  | Fbinop (op,f1,f2) ->
      let acc, f1 = fnF acc f1 in
      let acc, f2 = fnF acc f2 in
      acc, f_label_copy f (f_binary op f1 f2)
  | Fnot f1 ->
      let acc, f1 = fnF acc f1 in
      acc, f_label_copy f (f_not f1)
  | Ftrue | Ffalse ->
      acc, f
  | Fif (f1,f2,f3) ->
      let acc, f1 = fnF acc f1 in
      let acc, f2 = fnF acc f2 in
      let acc, f3 = fnF acc f3 in
      acc, f_label_copy f (f_if f1 f2 f3)
  | Flet (e,b) ->
      let acc, e = fnT acc e in
      let acc, b = bound_map_fold fnT fnF acc b in
      acc, f_label_copy f (f_let e b)
  | Fcase (e,bl) ->
      let acc, e = fnT acc e in
      let acc, bl = map_fold_left (bound_map_fold fnT fnF) acc bl in
      acc, f_label_copy f (f_case e bl)

(* replaces variables with de Bruijn indices in term [t] using map [m] *)

let rec t_abst m l lvl t = t_label_copy t (match t.t_node with
  | Tvar u -> begin try
      let i = Mvs.find u m in
      l := Sint.add i !l;
      t_bvar (i + lvl) t.t_ty
      with Not_found -> t end
  | Tlet (e, (u,b,t1)) ->
      let b,t1 = bnd_t_abst m l lvl b t1 in
      t_let (t_abst m l lvl e) (u,b,t1) t.t_ty
  | Tcase (e, bl) ->
      let br_abst (p,b,e) = let b,e = bnd_t_abst m l lvl b e in (p,b,e) in
      t_case (t_abst m l lvl e) (List.map br_abst bl) t.t_ty
  | Teps (u,b,f) ->
      let b,f = bnd_f_abst m l lvl b f in
      t_eps (u,b,f) t.t_ty
  | _ ->
      t_map_unsafe (t_abst m l lvl) (f_abst m l lvl) t)

and f_abst m l lvl f = f_label_copy f (match f.f_node with
  | Fquant (q, qf) ->
      f_quant q (bnd_q_abst m l lvl qf)
  | Flet (e, (u,b,f1)) ->
      let b,f1 = bnd_f_abst m l lvl b f1 in
      f_let (t_abst m l lvl e) (u,b,f1)
  | Fcase (e, bl) ->
      let br_abst (p,b,e) = let b,e = bnd_f_abst m l lvl b e in (p,b,e) in
      f_case (t_abst m l lvl e) (List.map br_abst bl)
  | _ ->
      f_map_unsafe (t_abst m l lvl) (f_abst m l lvl) f)

and bnd_t_abst m l lvl bv t =
  let l' = ref Sint.empty in
  let t = t_abst m l' (lvl + bv.bv_bound) t in
  update_bv m l lvl l' bv, t

and bnd_f_abst m l lvl bv f =
  let l' = ref Sint.empty in
  let f = f_abst m l' (lvl + bv.bv_bound) f in
  update_bv m l lvl l' bv, f

and bnd_q_abst m l lvl (vl,bv,tl,f) =
  let l' = ref Sint.empty and lvl' = lvl + bv.bv_bound in
  let tl = tr_map (t_abst m l' lvl') (f_abst m l' lvl') tl in
  let f = f_abst m l' lvl' f in
  vl, update_bv m l lvl l' bv, tl, f

and update_bv m l lvl l' bv =
  l := Sint.union !l' !l;
  let bv = bnd_map (t_abst m l lvl) bv in
  let add i acc = Sint.add (i + lvl) acc in
  { bv with bv_open = Sint.fold add !l' bv.bv_open }

let t_abst m t = t_abst m (ref Sint.empty) 0 t
let f_abst m f = f_abst m (ref Sint.empty) 0 f

(* replaces de Bruijn indices with variables in term [t] using map [m] *)

exception UnboundIndex

let bnd_find i m =
  try Mint.find i m with Not_found -> raise UnboundIndex

let bnd_inst m nv { bv_bound = d ; bv_open = b ; bv_defer = s } =
  let m = Mint.inter (fun _ () x -> Some x) b m in
  let m = Mint.translate ((+) d) m in
  let s = Mint.union (fun _ _ _ -> assert false) m s in
  { bv_bound = d + nv ; bv_open = Sint.empty ; bv_defer = s }

let rec t_inst m nv t = t_label_copy t (match t.t_node with
  | Tbvar i ->
      bnd_find i m
  | Tlet (e,(u,b,t1)) ->
      t_let (t_inst m nv e) (u, bound_inst m nv b, t1) t.t_ty
  | Tcase (e,bl) ->
      let br_inst (u,b,e) = (u, bound_inst m nv b, e) in
      t_case (t_inst m nv e) (List.map br_inst bl) t.t_ty
  | Teps (u,b,f) ->
      t_eps (u, bound_inst m nv b, f) t.t_ty
  | _ ->
      t_map_unsafe (t_inst m nv) (f_inst m nv) t)

and f_inst m nv f = f_label_copy f (match f.f_node with
  | Fquant (q,(vl,b,tl,f)) ->
      f_quant q (vl, bound_inst m nv b, tl, f)
  | Flet (e,(u,b,f1)) ->
      f_let (t_inst m nv e) (u, bound_inst m nv b, f1)
  | Fcase (e,bl) ->
      let br_inst (u,b,e) = (u, bound_inst m nv b, e) in
      f_case (t_inst m nv e) (List.map br_inst bl)
  | _ ->
      f_map_unsafe (t_inst m nv) (f_inst m nv) f)

and bound_inst m nv b = bnd_inst m nv (bnd_map (t_inst m nv) b)

(* close bindings *)

let bnd_new nv =
  { bv_bound = nv ; bv_open = Sint.empty ; bv_defer = Mint.empty }

let t_close_bound v t = (v, bnd_new 1, t_abst (Mvs.add v 0 Mvs.empty) t)
let f_close_bound v f = (v, bnd_new 1, f_abst (Mvs.add v 0 Mvs.empty) f)

let pat_varmap p =
  let i = ref (-1) in
  let rec mk_map acc p = match p.pat_node with
    | Pvar n -> incr i; Mvs.add n !i acc
    | Pas (p, n) -> incr i; mk_map (Mvs.add n !i acc) p
    | Por (p, _) -> mk_map acc p
    | _ -> pat_fold mk_map acc p
  in
  let m = mk_map Mvs.empty p in
  m, !i + 1

let t_close_branch pat t =
  let m,nv = pat_varmap pat in
  (pat, bnd_new nv, if nv = 0 then t else t_abst m t)

let f_close_branch pat f =
  let m,nv = pat_varmap pat in
  (pat, bnd_new nv, if nv = 0 then f else f_abst m f)

let f_close_quant vl tl f =
  if vl = [] then (vl, bnd_new 0, tl, f) else
  let i = ref (-1) in
  let add m v =
    if Mvs.mem v m then raise (DuplicateVar v);
    incr i; Mvs.add v !i m
  in
  let m = List.fold_left add Mvs.empty vl in
  (vl, bnd_new (!i + 1), tr_map (t_abst m) (f_abst m) tl, f_abst m f)

(* open bindings *)

let t_open_bound (v,b,t) =
  let v = fresh_vsymbol v in
  v, t_inst (Mint.add 0 (t_var v) b.bv_defer) b.bv_bound t

let f_open_bound (v,b,f) =
  let v = fresh_vsymbol v in
  v, f_inst (Mint.add 0 (t_var v) b.bv_defer) b.bv_bound f

let rec pat_rename ns p = match p.pat_node with
  | Pvar n -> pat_var (Mvs.find n ns)
  | Pas (p, n) -> pat_as (pat_rename ns p) (Mvs.find n ns)
  | _ -> pat_map (pat_rename ns) p

let pat_substs p s =
  let m, _ = pat_varmap p in
  Mvs.fold (fun x i (s, ns) ->
    let x' = fresh_vsymbol x in
    Mint.add i (t_var x') s, Mvs.add x x' ns) m (s, Mvs.empty)

let t_open_branch (p,b,t) =
  if b.bv_bound = 0 then (p, t) else
  let m,ns = pat_substs p b.bv_defer in
  pat_rename ns p, t_inst m b.bv_bound t

let f_open_branch (p,b,f) =
  if b.bv_bound = 0 then (p, f) else
  let m,ns = pat_substs p b.bv_defer in
  pat_rename ns p, f_inst m b.bv_bound f

let quant_vars vl s =
  let i = ref (-1) in
  let add m v = let v = fresh_vsymbol v in
    incr i; Mint.add !i (t_var v) m, v in
  map_fold_left add s vl

let f_open_quant (vl,b,tl,f) =
  if b.bv_bound = 0 then (vl, tl, f) else
  let m,vl = quant_vars vl b.bv_defer and nv = b.bv_bound in
  (vl, tr_map (t_inst m nv) (f_inst m nv) tl, f_inst m nv f)

let rec f_open_forall f = match f.f_node with
  | Fquant (Fforall, f) ->
      let vl, _, f = f_open_quant f in
      let vl', f = f_open_forall f in
      vl@vl', f
  | _ -> [], f

let rec f_open_exists f = match f.f_node with
  | Fquant (Fexists, f) ->
      let vl, _, f = f_open_quant f in
      let vl', f = f_open_exists f in
      vl@vl', f
  | _ -> [], f

(** open bindings with optimized closing callbacks *)

let t_open_bound_cb tb =
  let v, t = t_open_bound tb in
  let close v' t' =
    if t_equal t t' && vs_equal v v' then tb else t_close_bound v' t'
  in
  v, t, close

let f_open_bound_cb fb =
  let v, f = f_open_bound fb in
  let close v' f' =
    if f_equal f f' && vs_equal v v' then fb else f_close_bound v' f'
  in
  v, f, close

let t_open_branch_cb tbr =
  let p, t = t_open_branch tbr in
  let close p' t' =
    if t_equal t t' && pat_equal p p' then tbr else t_close_branch p' t'
  in
  p, t, close

let f_open_branch_cb fbr =
  let p, f = f_open_branch fbr in
  let close p' f' =
    if f_equal f f' && pat_equal p p' then fbr else f_close_branch p' f'
  in
  p, f, close

let f_open_quant_cb fq =
  let vl, tl, f = f_open_quant fq in
  let close vl' tl' f' =
    if f_equal f f' && tr_equal tl tl' && list_all2 vs_equal vl vl'
    then fq else f_close_quant vl' tl' f'
  in
  vl, tl, f, close

(* constructors with type checking *)

let ls_app_inst ls tl ty =
  let s = match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> ty_match Mtv.empty vty ty
    | None, None -> Mtv.empty
  in
  let s =
    let mtch s ty t = ty_match s ty t.t_ty in
    try List.fold_left2 mtch s ls.ls_args tl
    with Invalid_argument _ -> raise (BadArity
     (ls, List.length ls.ls_args, List.length tl))
  in
  let add v acc = Mtv.add v (ty_inst s (ty_var v)) acc in
  Stv.fold add (ls_ty_freevars ls) Mtv.empty

let fs_app_inst fs tl ty = ls_app_inst fs tl (Some ty)
let ps_app_inst ps tl    = ls_app_inst ps tl None

let t_app fs tl ty = ignore (fs_app_inst fs tl ty); t_app fs tl ty

let f_app ps tl = ignore (ps_app_inst ps tl); f_app ps tl

let t_app_infer fs tl =
  let mtch s ty t = ty_match s ty t.t_ty in
  let s =
    try List.fold_left2 mtch Mtv.empty fs.ls_args tl
    with Invalid_argument _ -> raise (BadArity
      (fs, List.length fs.ls_args, List.length tl))
  in
  let ty = match fs.ls_value with
    | Some ty -> ty_inst s ty
    | _ -> raise (FunctionSymbolExpected fs)
  in
  t_app fs tl ty

exception EmptyCase

let t_case t bl =
  let ty = match bl with
    | (_,_,tbr) :: _ -> tbr.t_ty
    | _ -> raise EmptyCase
  in
  let t_check_branch (p,_,tbr) =
    check_ty_equal p.pat_ty t.t_ty;
    check_ty_equal ty tbr.t_ty
  in
  List.iter t_check_branch bl;
  t_case t bl ty

let f_case t bl =
  if bl = [] then raise EmptyCase;
  let f_check_branch (p,_,_) =
    check_ty_equal p.pat_ty t.t_ty
  in
  List.iter f_check_branch bl;
  f_case t bl

let t_if f t1 t2 =
  check_ty_equal t1.t_ty t2.t_ty;
  t_if f t1 t2

let t_let t1 ((v,_,t2) as bt) =
  check_ty_equal v.vs_ty t1.t_ty;
  t_let t1 bt t2.t_ty

let f_let t1 ((v,_,_) as bf) =
  check_ty_equal v.vs_ty t1.t_ty;
  f_let t1 bf

let t_eps ((v,_,_) as bf) =
  t_eps bf v.vs_ty

let t_const c = match c with
  | ConstInt _ -> t_const c ty_int
  | ConstReal _ -> t_const c ty_real

let f_quant q ((vl,_,_,f) as qf) =
  if vl = [] then f else f_quant q qf

let f_forall = f_quant Fforall
let f_exists = f_quant Fexists

(* closing constructors *)

let f_quant_close q vl tl f =
  if vl = [] then f else f_quant q (f_close_quant vl tl f)

let f_forall_close = f_quant_close Fforall
let f_exists_close = f_quant_close Fexists

let t_let_close v t1 t2 = t_let t1 (t_close_bound v t2)
let f_let_close v t1 f2 = f_let t1 (f_close_bound v f2)

let t_eps_close v f = t_eps (f_close_bound v f)

(* built-in symbols *)

let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix =") [v; v]

let f_equ t1 t2 = f_app ps_equ [t1; t2]
let f_neq t1 t2 = f_not (f_app ps_equ [t1; t2])

let fs_func_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_b = ty_var (create_tvsymbol (id_fresh "b")) in
  create_fsymbol (id_fresh "infix @!") [ty_func ty_a ty_b; ty_a] ty_b

let ps_pred_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix @?") [ty_pred ty_a; ty_a]

let t_func_app fn t = t_app_infer fs_func_app [fn; t]
let f_pred_app pr t = f_app ps_pred_app [pr; t]

let t_func_app_l = List.fold_left t_func_app

let f_pred_app_l pr tl = match List.rev tl with
  | t::tl -> f_pred_app (t_func_app_l pr (List.rev tl)) t
  | _ -> Pervasives.invalid_arg "f_pred_app_l"

let fs_tuple = Util.memo_int 17 (fun n ->
  let tyl = ref [] in
  for i = 1 to n
  do tyl := ty_var (create_tvsymbol (id_fresh "a")) :: !tyl done;
  let ty = ty_tuple !tyl in
  create_fsymbol (id_fresh ("Tuple" ^ string_of_int n)) !tyl ty)

let is_fs_tuple fs = fs == fs_tuple (List.length fs.ls_args)

let t_tuple tl =
  let ty = ty_tuple (List.map (fun t -> t.t_ty) tl) in
  t_app (fs_tuple (List.length tl)) tl ty

(** Term library *)

(* generic map over types, symbols and variables *)

let rec t_gen_map fnT fnB fnV fnL t =
  let fn_t = t_gen_map fnT fnB fnV fnL in
  let fn_f = f_gen_map fnT fnB fnV fnL in
  let ty = fnT t.t_ty in
  t_label_copy t (match t.t_node with
    | Tbvar n -> t_bvar n ty
    | Tvar v -> fnV v ty
    | Tconst _ -> t
    | Tapp (f, tl) -> t_app (fnL f) (List.map fn_t tl) ty
    | Tif (f, t1, t2) -> t_if (fn_f f) (fn_t t1) (fn_t t2)
    | Tlet (t1, (u,b,t2)) ->
        let t1 = fn_t t1 in
        t_let t1 (fnB u t1.t_ty, bnd_map fn_t b, fn_t t2)
    | Tcase (t1, bl) ->
        let br (p,b,t) = pat_gen_map fnT fnB fnL p, bnd_map fn_t b, fn_t t in
        t_case (fn_t t1) (List.map br bl)
    | Teps (u,b,f) ->
        t_eps (fnB u ty, bnd_map fn_t b, fn_f f))

and f_gen_map fnT fnB fnV fnL f =
  let fn_t = t_gen_map fnT fnB fnV fnL in
  let fn_f = f_gen_map fnT fnB fnV fnL in
  f_label_copy f (match f.f_node with
    | Fapp (p, tl) -> f_app (fnL p) (List.map fn_t tl)
    | Fquant (q, (vl,b,tl,f1)) ->
        let vl = List.map (fun u -> fnB u (fnT u.vs_ty)) vl in
        f_quant q (vl, bnd_map fn_t b, tr_map fn_t fn_f tl, fn_f f1)
    | Fbinop (op, f1, f2) -> f_binary op (fn_f f1) (fn_f f2)
    | Fnot f1 -> f_not (fn_f f1)
    | Ftrue | Ffalse -> f
    | Fif (f1, f2, f3) -> f_if (fn_f f1) (fn_f f2) (fn_f f3)
    | Flet (t, (u,b,f1)) ->
        let t1 = fn_t t in
        f_let t1 (fnB u t1.t_ty, bnd_map fn_t b, fn_f f1)
    | Fcase (t, bl) ->
        let br (p,b,f) = pat_gen_map fnT fnB fnL p, bnd_map fn_t b, fn_f f in
        f_case (fn_t t) (List.map br bl))

let get_fnT fn = Wty.memoize 17 (fun ty -> ty_s_map fn ty)

let get_fnB () =
  let ht = Hid.create 17 in
  let fnV vs ty =
    if ty_equal vs.vs_ty ty then vs else
      try Hid.find ht vs.vs_name with Not_found ->
        let nv = create_vsymbol (id_dup vs.vs_name) ty in
        Hid.add ht vs.vs_name nv;
        nv
  in
  fnV

let get_fnV () =
  let fnB = get_fnB () in
  fun vs ty -> t_var (fnB vs ty)

let t_s_map fnT fnL t = t_gen_map (get_fnT fnT) (get_fnB ()) (get_fnV ()) fnL t
let f_s_map fnT fnL f = f_gen_map (get_fnT fnT) (get_fnB ()) (get_fnV ()) fnL f

(* simultaneous substitution into types and terms *)

let t_ty_subst mapT mapV t =
  let fnV vs _ty = try Mvs.find vs mapV with Not_found -> t_var vs in
  t_gen_map (ty_inst mapT) (get_fnB ()) fnV (fun ls -> ls) t

let f_ty_subst mapT mapV f =
  let fnV vs _ty = try Mvs.find vs mapV with Not_found -> t_var vs in
  f_gen_map (ty_inst mapT) (get_fnB ()) fnV (fun ls -> ls) f

(* fold over symbols *)

let rec t_gen_fold fnT fnB fnV fnL acc t =
  let fn_t = t_gen_fold fnT fnB fnV fnL in
  let fn_f = f_gen_fold fnT fnB fnV fnL in
  let acc = fnT acc t.t_ty in
  match t.t_node with
  | Tbvar _ | Tconst _ -> acc
  | Tvar v -> fnV acc v
  | Tapp (f, tl) -> List.fold_left fn_t (fnL acc f) tl
  | Tif (f, t1, t2) -> fn_t (fn_t (fn_f acc f) t1) t2
  | Tlet (t1, (u,b,t2)) -> fn_t (bnd_fold fn_t (fn_t (fnB acc u) t1) b) t2
  | Tcase (t1, bl) ->
      let branch acc (p,b,t) =
        fn_t (pat_gen_fold fnT fnB fnL (bnd_fold fn_t acc b) p) t in
      List.fold_left branch (fn_t acc t1) bl
  | Teps (u,b,f) -> fn_f (bnd_fold fn_t (fnB acc u) b) f

and f_gen_fold fnT fnB fnV fnL acc f =
  let fn_t = t_gen_fold fnT fnB fnV fnL in
  let fn_f = f_gen_fold fnT fnB fnV fnL in
  match f.f_node with
  | Fapp (p, tl) -> List.fold_left fn_t (fnL acc p) tl
  | Fquant (_, (vl,b,tl,f1)) ->
      let fn_v acc u = fnB (fnT acc u.vs_ty) u in
      let acc = List.fold_left fn_v acc vl in
      fn_f (tr_fold fn_t fn_f (bnd_fold fn_t acc b) tl) f1
  | Fbinop (_, f1, f2) -> fn_f (fn_f acc f1) f2
  | Fnot f1 -> fn_f acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fn_f (fn_f (fn_f acc f1) f2) f3
  | Flet (t, (u,b,f1)) -> fn_f (bnd_fold fn_t (fn_t (fnB acc u) t) b) f1
  | Fcase (t, bl) ->
      let branch acc (p,b,f) =
        fn_f (pat_gen_fold fnT fnB fnL (bnd_fold fn_t acc b) p) f in
      List.fold_left branch (fn_t acc t) bl

let t_s_fold fnT fnL acc t =
  t_gen_fold (ty_s_fold fnT) Util.const Util.const fnL acc t

let f_s_fold fnT fnL acc f =
  f_gen_fold (ty_s_fold fnT) Util.const Util.const fnL acc f

let t_s_all prT prL t =
  try t_s_fold (all_fn prT) (all_fn prL) true t with FoldSkip -> false

let f_s_all prT prL f =
  try f_s_fold (all_fn prT) (all_fn prL) true f with FoldSkip -> false

let t_s_any prT prL t =
  try t_s_fold (any_fn prT) (any_fn prL) false t with FoldSkip -> true

let f_s_any prT prL f =
  try f_s_fold (any_fn prT) (any_fn prL) false f with FoldSkip -> true

(* free type variables *)

let t_ty_freevars s t =
  t_gen_fold ty_freevars Util.const Util.const Util.const s t

let f_ty_freevars s f =
  f_gen_fold ty_freevars Util.const Util.const Util.const s f

(* safe opening map *)

let t_bound  fn b = let u,t,close = t_open_bound_cb  b in close u (fn t)
let f_bound  fn b = let u,f,close = f_open_bound_cb  b in close u (fn f)
let t_branch fn b = let p,t,close = t_open_branch_cb b in close p (fn t)
let f_branch fn b = let p,f,close = f_open_branch_cb b in close p (fn f)

let t_map fnT fnF t = t_label_copy t (match t.t_node with
  | Tlet (t1, b) -> t_let (fnT t1) (t_bound fnT b)
  | Tcase (t1, bl) -> t_case (fnT t1) (List.map (t_branch fnT) bl)
  | Teps b -> t_eps (f_bound fnF b)
  | _ -> t_map_unsafe fnT fnF t)

let f_map fnT fnF f = f_label_copy f (match f.f_node with
  | Fquant (q, b) ->
      let vl, tl, f1, close = f_open_quant_cb b in
      f_quant q (close vl (tr_map fnT fnF tl) (fnF f1))
  | Flet (t, b) -> f_let (fnT t) (f_bound fnF b)
  | Fcase (t, bl) -> f_case (fnT t) (List.map (f_branch fnF) bl)
  | _ -> f_map_unsafe fnT fnF f)

let protect fn t =
  let res = fn t in
  check_ty_equal t.t_ty res.t_ty;
  res

let t_map fnT = t_map (protect fnT)
let f_map fnT = f_map (protect fnT)

let f_map_sign fnT fnF sign f = f_label_copy f (match f.f_node with
  | Fbinop (Fimplies, f1, f2) ->
      f_implies (fnF (not sign) f1) (fnF sign f2)
  | Fbinop (Fiff, f1, f2) ->
      let f1p = fnF sign f1 in let f1n = fnF (not sign) f1 in
      let f2p = fnF sign f2 in let f2n = fnF (not sign) f2 in
      if f_equal f1p f1n && f_equal f2p f2n then f_iff f1p f2p
      else if sign
        then f_and (f_implies f1n f2p) (f_implies f2n f1p)
        else f_implies (f_or f1n f2n) (f_and f1p f2p)
  | Fnot f1 ->
      f_not (fnF (not sign) f1)
  | Fif (f1, f2, f3) ->
      let f1p = fnF sign f1 in let f1n = fnF (not sign) f1 in
      let f2 = fnF sign f2 in let f3 = fnF sign f3 in
      if f_equal f1p f1n then f_if f1p f2 f3 else if sign
        then f_and (f_implies f1n f2) (f_implies (f_not f1p) f3)
        else f_or (f_and f1p f2) (f_and (f_not f1n) f3)
  | _ -> f_map fnT (fnF sign) f)

(* safe opening fold *)

let t_branch fn acc b = let _,t = t_open_branch b in fn acc t
let f_branch fn acc b = let _,f = f_open_branch b in fn acc f

let t_fold fnT fnF acc t = match t.t_node with
  | Tlet (t1, b) -> let _,t2 = t_open_bound b in fnT (fnT acc t1) t2
  | Tcase (t1, bl) -> List.fold_left (t_branch fnT) (fnT acc t1) bl
  | Teps b -> let _,f = f_open_bound b in fnF acc f
  | _ -> t_fold_unsafe fnT fnF acc t

let f_fold fnT fnF acc f = match f.f_node with
  | Fquant (_, b) ->
      let _, tl, f1 = f_open_quant b in tr_fold fnT fnF (fnF acc f1) tl
  | Flet (t, b) -> let _,f1 = f_open_bound b in fnF (fnT acc t) f1
  | Fcase (t, bl) -> List.fold_left (f_branch fnF) (fnT acc t) bl
  | _ -> f_fold_unsafe fnT fnF acc f

let t_all prT prF t =
  try t_fold (all_fn prT) (all_fn prF) true t with FoldSkip -> false

let f_all prT prF f =
  try f_fold (all_fn prT) (all_fn prF) true f with FoldSkip -> false

let t_any prT prF t =
  try t_fold (any_fn prT) (any_fn prF) false t with FoldSkip -> true

let f_any prT prF f =
  try f_fold (any_fn prT) (any_fn prF) false f with FoldSkip -> true

(* safe opening map_fold *)

let t_bound fn acc b =
  let u,t,close = t_open_bound_cb  b in let acc,t = fn acc t in acc, close u t

let f_bound fn acc b =
  let u,f,close = f_open_bound_cb  b in let acc,f = fn acc f in acc, close u f

let t_branch fn acc b =
  let p,t,close = t_open_branch_cb b in let acc,t = fn acc t in acc, close p t

let f_branch fn acc b =
  let p,f,close = f_open_branch_cb b in let acc,f = fn acc f in acc, close p f

let t_map_fold fnT fnF acc t = match t.t_node with
  | Tlet (e,b) ->
      let acc, e = fnT acc e in
      let acc, b = t_bound fnT acc b in
      acc, t_label_copy t (t_let e b)
  | Tcase (e,bl) ->
      let acc, e = fnT acc e in
      let acc, bl = map_fold_left (t_branch fnT) acc bl in
      acc, t_label_copy t (t_case e bl)
  | Teps b ->
      let acc, b = f_bound fnF acc b in
      acc, t_label_copy t (t_eps b)
  | _ -> t_map_fold_unsafe fnT fnF acc t

let f_map_fold fnT fnF acc f = match f.f_node with
  | Fquant (q,b) ->
      let vl,tl,f1,close = f_open_quant_cb b in
      let acc, tl = tr_map_fold fnT fnF acc tl in
      let acc, f1 = fnF acc f1 in
      acc, f_label_copy f (f_quant q (close vl tl f1))
  | Flet (e,b) ->
      let acc, e = fnT acc e in
      let acc, b = f_bound fnF acc b in
      acc, f_label_copy f (f_let e b)
  | Fcase (e,bl) ->
      let acc, e = fnT acc e in
      let acc, bl = map_fold_left (f_branch fnF) acc bl in
      acc, f_label_copy f (f_case e bl)
  | _ -> f_map_fold_unsafe fnT fnF acc f

let protect_fold fn acc t =
  let acc,res = fn acc t in
  check_ty_equal t.t_ty res.t_ty;
  acc,res

let t_map_fold fnT = t_map_fold (protect_fold fnT)
let f_map_fold fnT = f_map_fold (protect_fold fnT)

(* continuation-passing traversal *)

let rec list_map_cont fnL contL = function
  | e::el ->
      let cont_l e el = contL (e::el) in
      let cont_e e = list_map_cont fnL (cont_l e) el in
      fnL cont_e e
  | [] ->
      contL []

let expr_map_cont fnT fnF contE = function
  | Term t -> fnT (fun t -> contE (Term t)) t
  | Fmla f -> fnF (fun f -> contE (Fmla f)) f

let tr_map_cont fnT fnF =
  list_map_cont (list_map_cont (expr_map_cont fnT fnF))

let t_map_cont fnT fnF contT t =
  let contT e = contT (t_label_copy t e) in
  match t.t_node with
  | Tbvar _ -> raise UnboundIndex
  | Tvar _ | Tconst _ -> contT t
  | Tapp (fs, tl) ->
      let cont_app tl = contT (t_app fs tl t.t_ty) in
      list_map_cont fnT cont_app tl
  | Tif (f, t1, t2) ->
      let cont_else f t1 t2 = contT (t_if f t1 t2) in
      let cont_then f t1 = fnT (cont_else f t1) t2 in
      let cont_if f = fnT (cont_then f) t1 in
      fnF cont_if f
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let cont_in t1 t2 = contT (t_let t1 (close u t2)) in
      let cont_let t1 = fnT (cont_in t1) t2 in
      fnT cont_let t1
  | Tcase (t1, bl) ->
      let fnB contB b =
        let pat,t,close = t_open_branch_cb b in
        fnT (fun t -> contB (close pat t)) t
      in
      let cont_with t1 bl = contT (t_case t1 bl) in
      let cont_case t1 = list_map_cont fnB (cont_with t1) bl in
      fnT cont_case t1
  | Teps b ->
      let u,f,close = f_open_bound_cb b in
      let cont_eps f = contT (t_eps (close u f)) in
      fnF cont_eps f

let f_map_cont fnT fnF contF f =
  let contF e = contF (f_label_copy f e) in
  match f.f_node with
  | Fapp (ps, tl) ->
      let cont_app tl = contF (f_app ps tl) in
      list_map_cont fnT cont_app tl
  | Fquant (q, b) ->
      let vl, tl, f1, close = f_open_quant_cb b in
      let cont_dot tl f1 = contF (f_quant q (close vl tl f1)) in
      let cont_quant tl = fnF (cont_dot tl) f1 in
      tr_map_cont fnT fnF cont_quant tl
  | Fbinop (op, f1, f2) ->
      let cont_r f1 f2 = contF (f_binary op f1 f2) in
      let cont_l f1 = fnF (cont_r f1) f2 in
      fnF cont_l f1
  | Fnot f1 ->
      let cont_not f1 = contF (f_not f1) in
      fnF cont_not f1
  | Ftrue | Ffalse -> contF f
  | Fif (f1, f2, f3) ->
      let cont_else f1 f2 f3 = contF (f_if f1 f2 f3) in
      let cont_then f1 f2 = fnF (cont_else f1 f2) f3 in
      let cont_if f1 = fnF (cont_then f1) f2 in
      fnF cont_if f1
  | Flet (t1, b) ->
      let u,f2,close = f_open_bound_cb b in
      let cont_in t1 f2 = contF (f_let t1 (close u f2)) in
      let cont_let t1 = fnF (cont_in t1) f2 in
      fnT cont_let t1
  | Fcase (t1, bl) ->
      let fnB contB b =
        let pat,f,close = f_open_branch_cb b in
        fnF (fun f -> contB (close pat f)) f
      in
      let cont_with t1 bl = contF (f_case t1 bl) in
      let cont_case t1 = list_map_cont fnB (cont_with t1) bl in
      fnT cont_case t1

let protect_cont t contT e =
  check_ty_equal t.t_ty e.t_ty;
  contT e

let t_map_cont fnT = t_map_cont (fun c t -> fnT (protect_cont t c) t)
let f_map_cont fnT = f_map_cont (fun c t -> fnT (protect_cont t c) t)

(* map/fold over free variables *)

let rec t_v_map fn t = match t.t_node with
  | Tvar u ->
      let res = fn u in
      check_ty_equal t.t_ty res.t_ty;
      res
  | _ ->
      t_map_unsafe (t_v_map fn) (f_v_map fn) t

and f_v_map fn f = f_map_unsafe (t_v_map fn) (f_v_map fn) f

let rec t_v_fold fn acc t = match t.t_node with
  | Tvar u -> fn acc u
  | _ -> t_fold_unsafe (t_v_fold fn) (f_v_fold fn) acc t

and f_v_fold fn acc f = f_fold_unsafe (t_v_fold fn) (f_v_fold fn) acc f

let t_v_all pr t = try t_v_fold (all_fn pr) true t with FoldSkip -> false
let f_v_all pr f = try f_v_fold (all_fn pr) true f with FoldSkip -> false
let t_v_any pr t = try t_v_fold (any_fn pr) false t with FoldSkip -> true
let f_v_any pr f = try f_v_fold (any_fn pr) false f with FoldSkip -> true

(* looks for occurrence of a variable from set [s] in a term [t] *)

let t_occurs s t = not (Svs.is_empty s) && t_v_any (fun u -> Svs.mem u s) t
let f_occurs s f = not (Svs.is_empty s) && f_v_any (fun u -> Svs.mem u s) f

let t_occurs_single v t = t_v_any (vs_equal v) t
let f_occurs_single v f = f_v_any (vs_equal v) f

(* replaces variables with terms in term [t] using map [m] *)

let find_vs m u = try Mvs.find u m with Not_found -> t_var u

let t_subst m t = if Mvs.is_empty m then t else t_v_map (find_vs m) t
let f_subst m f = if Mvs.is_empty m then f else f_v_map (find_vs m) f

let eq_vs v t u = if vs_equal u v then t else t_var u

let t_subst_single v t1 t = t_v_map (eq_vs v t1) t
let f_subst_single v t1 f = f_v_map (eq_vs v t1) f

(* set of free variables *)

let t_freevars s t = t_v_fold (fun s u -> Svs.add u s) s t
let f_freevars s f = f_v_fold (fun s u -> Svs.add u s) s f

(* alpha-equality on patterns *)

let rec pat_equal_alpha p1 p2 =
  pat_equal p1 p2 ||
  ty_equal p1.pat_ty p2.pat_ty &&
  match p1.pat_node, p2.pat_node with
  | Pwild, Pwild | Pvar _, Pvar _ -> true
  | Papp (f1, l1), Papp (f2, l2) ->
      ls_equal f1 f2 && List.for_all2 pat_equal_alpha l1 l2
  | Pas (p1, _), Pas (p2, _) -> pat_equal_alpha p1 p2
  | Por (p1, q1), Por (p2, q2) ->
      pat_equal_alpha p1 p2 && pat_equal_alpha q1 q2
  | _ -> false

(* alpha-equality on terms and formulas *)

let bound_equal_alpha fnE m1 m2 (v1,b1,e1) (v2,b2,e2) =
  ty_equal v1.vs_ty v2.vs_ty &&
  let vn = t_var (fresh_vsymbol v1) in
  let m1 = bound_inst m1.bv_defer m1.bv_bound b1 in
  let m2 = bound_inst m2.bv_defer m2.bv_bound b2 in
  let m1 = { m1 with bv_defer = Mint.add 0 vn m1.bv_defer } in
  let m2 = { m2 with bv_defer = Mint.add 0 vn m2.bv_defer } in
  fnE m1 m2 e1 e2

let branch_equal_alpha fnE m1 m2 (p1,b1,e1) (p2,b2,e2) =
  pat_equal_alpha p1 p2 &&
  let mn,_ = pat_substs p1 Mint.empty in
  let m1 = bound_inst m1.bv_defer m1.bv_bound b1 in
  let m2 = bound_inst m2.bv_defer m2.bv_bound b2 in
  let m1 = { m1 with bv_defer = Mint.fold Mint.add mn m1.bv_defer } in
  let m2 = { m2 with bv_defer = Mint.fold Mint.add mn m2.bv_defer } in
  fnE m1 m2 e1 e2

let quant_equal_alpha fnF m1 m2 (vl1,b1,_,f1) (vl2,b2,_,f2) =
  list_all2 (fun v1 v2 -> ty_equal v1.vs_ty v2.vs_ty) vl1 vl2 &&
  let mn,_ = quant_vars vl1 Mint.empty in
  let m1 = bound_inst m1.bv_defer m1.bv_bound b1 in
  let m2 = bound_inst m2.bv_defer m2.bv_bound b2 in
  let m1 = { m1 with bv_defer = Mint.fold Mint.add mn m1.bv_defer } in
  let m2 = { m2 with bv_defer = Mint.fold Mint.add mn m2.bv_defer } in
  fnF m1 m2 f1 f2

let rec t_equal_alpha m1 m2 t1 t2 =
  t_equal t1 t2 || ty_equal t1.t_ty t2.t_ty &&
  let t_eq = t_equal_alpha m1 m2 in
  let f_eq = f_equal_alpha m1 m2 in
  match t1.t_node, t2.t_node with
    | Tbvar i, _ ->
        t_equal_alpha (bnd_new 0) m2 (bnd_find i m1.bv_defer) t2
    | _, Tbvar i ->
        t_equal_alpha m1 (bnd_new 0) t1 (bnd_find i m2.bv_defer)
    | Tvar v1, Tvar v2 ->
        vs_equal v1 v2
    | Tconst c1, Tconst c2 ->
        c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_eq l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        f_eq f1 f2 && t_eq t1 t2 && t_eq e1 e2
    | Tlet (t1,tb1), Tlet (t2,tb2) ->
        t_eq t1 t2 && bound_equal_alpha t_equal_alpha m1 m2 tb1 tb2
    | Tcase (t1,b1), Tcase (t2,b2) ->
        t_eq t1 t2 && list_all2 (branch_equal_alpha t_equal_alpha m1 m2) b1 b2
    | Teps fb1, Teps fb2 ->
        bound_equal_alpha f_equal_alpha m1 m2 fb1 fb2
    | _ -> false

and f_equal_alpha m1 m2 f1 f2 =
  f_equal f1 f2 ||
  let t_eq = t_equal_alpha m1 m2 in
  let f_eq = f_equal_alpha m1 m2 in
  match f1.f_node, f2.f_node with
    | Fapp (s1,l1), Fapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_eq l1 l2
    | Fquant (q1,b1), Fquant (q2,b2) ->
        q1 = q2 && quant_equal_alpha f_equal_alpha m1 m2 b1 b2
    | Fbinop (a,f1,g1), Fbinop (b,f2,g2) ->
        a = b && f_eq f1 f2 && f_eq g1 g2
    | Fnot f1, Fnot f2 ->
        f_eq f1 f2
    | Ftrue, Ftrue | Ffalse, Ffalse ->
        true
    | Fif (f1,g1,h1), Fif (f2,g2,h2) ->
        f_eq f1 f2 && f_eq g1 g2 && f_eq h1 h2
    | Flet (t1,fb1), Flet (t2,fb2) ->
        t_eq t1 t2 && bound_equal_alpha f_equal_alpha m1 m2 fb1 fb2
    | Fcase (t1,b1), Fcase (t2,b2) ->
        t_eq t1 t2 && list_all2 (branch_equal_alpha f_equal_alpha m1 m2) b1 b2
    | _ -> false

let t_equal_alpha = t_equal_alpha (bnd_new 0) (bnd_new 0)
let f_equal_alpha = f_equal_alpha (bnd_new 0) (bnd_new 0)

(* binder-free term/formula matching *)

exception NoMatch

let rec t_match s t1 t2 =
  if t_equal t1 t2 then s else
  if not (t_equal t1.t_ty t2.t_ty) then raise NoMatch else
  match t1.t_node, t2.t_node with
    | Tconst c1, Tconst c2 when c1 = c2 -> s
    | Tvar v1, _ ->
        Mvs.change v1 (function
          | None -> Some t2
          | Some t1 as r when t_equal t1 t2 -> r
          | _ -> raise NoMatch) s
    | Tapp (s1,l1), Tapp (s2,l2) when ls_equal s1 s2 ->
        List.fold_left2 t_match s l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        t_match (t_match (f_match s f1 f2) t1 t2) e1 e2
    | _ -> raise NoMatch

and f_match s f1 f2 =
  if f_equal f1 f2 then s else
  match f1.f_node, f2.f_node with
    | Fapp (s1,l1), Fapp (s2,l2) when ls_equal s1 s2 ->
        List.fold_left2 t_match s l1 l2
    | Fbinop (op1,f1,g1), Fbinop (op2,f2,g2) when op1 = op2 ->
        f_match (f_match s f1 f2) g1 g2
    | Fnot f1, Fnot f2 ->
        f_match s f1 f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        s
    | Fif (f1,g1,h1), Fif (f2,g2,h2) ->
        f_match (f_match (f_match s f1 f2) g1 g2) h1 h2
    | _ -> raise NoMatch

(* occurrence check *)

let rec t_occurs_term r t = t_equal r t ||
  t_any (t_occurs_term r) (f_occurs_term r) t

and f_occurs_term r f =
  f_any (t_occurs_term r) (f_occurs_term r) f

let rec t_occurs_fmla r t =
  t_any (t_occurs_fmla r) (f_occurs_fmla r) t

and f_occurs_fmla r f = f_equal r f ||
  f_any (t_occurs_fmla r) (f_occurs_fmla r) f

(* occurrence check modulo alpha *)

let rec t_occurs_term_alpha r t = t_equal_alpha r t ||
  t_any (t_occurs_term_alpha r) (f_occurs_term_alpha r) t

and f_occurs_term_alpha r f =
  f_any (t_occurs_term_alpha r) (f_occurs_term_alpha r) f

let rec t_occurs_fmla_alpha r t =
  t_any (t_occurs_fmla_alpha r) (f_occurs_fmla_alpha r) t

and f_occurs_fmla_alpha r f = f_equal_alpha r f ||
  f_any (t_occurs_fmla_alpha r) (f_occurs_fmla_alpha r) f

(* substitutes term [t2] for term [t1] in term [t] *)

let rec t_subst_term t1 t2 t = if t_equal t t1 then t2 else
  t_map (t_subst_term t1 t2) (f_subst_term t1 t2) t

and f_subst_term t1 t2 f =
  f_map (t_subst_term t1 t2) (f_subst_term t1 t2) f

let t_subst_term t1 t2 t =
  check_ty_equal t1.t_ty t2.t_ty;
  t_subst_term t1 t2 t

let f_subst_term t1 t2 f =
  check_ty_equal t1.t_ty t2.t_ty;
  f_subst_term t1 t2 f

(* substitutes fmla [f2] for fmla [f1] in term [t] *)

let rec t_subst_fmla f1 f2 t =
  t_map (t_subst_fmla f1 f2) (f_subst_fmla f1 f2) t

and f_subst_fmla f1 f2 f = if f_equal f f1 then f2 else
  f_map (t_subst_fmla f1 f2) (f_subst_fmla f1 f2) f

(* substitutes term [t2] for term [t1] in term [t] modulo alpha *)

let rec t_subst_term_alpha t1 t2 t = if t_equal_alpha t t1 then t2 else
  t_map (t_subst_term_alpha t1 t2) (f_subst_term_alpha t1 t2) t

and f_subst_term_alpha t1 t2 f =
  f_map (t_subst_term_alpha t1 t2) (f_subst_term_alpha t1 t2) f

let t_subst_term_alpha t1 t2 t =
  check_ty_equal t1.t_ty t2.t_ty;
  t_subst_term_alpha t1 t2 t

let f_subst_term_alpha t1 t2 f =
  check_ty_equal t1.t_ty t2.t_ty;
  f_subst_term_alpha t1 t2 f

(* substitutes fmla [f2] for fmla [f1] in term [t] modulo alpha *)

let rec t_subst_fmla_alpha f1 f2 t =
  t_map (t_subst_fmla_alpha f1 f2) (f_subst_fmla_alpha f1 f2) t

and f_subst_fmla_alpha f1 f2 f = if f_equal_alpha f f1 then f2 else
  f_map (t_subst_fmla_alpha f1 f2) (f_subst_fmla_alpha f1 f2) f

(* constructors with propositional simplification *)

let f_not_simp f = match f.f_node with
  | Ftrue  -> f_false
  | Ffalse -> f_true
  | Fnot f -> f
  | _      -> f_not f

let f_and_simp f1 f2 = match f1.f_node, f2.f_node with
  | Ftrue, _  -> f2
  | _, Ftrue  -> f1
  | Ffalse, _ -> f1
  | _, Ffalse -> f2
  | _, _      -> if f_equal f1 f2 then f1 else f_and f1 f2

let f_and_simp_l l = List.fold_left f_and_simp f_true l

let f_or_simp f1 f2 = match f1.f_node, f2.f_node with
  | Ftrue, _  -> f1
  | _, Ftrue  -> f2
  | Ffalse, _ -> f2
  | _, Ffalse -> f1
  | _, _      -> if f_equal f1 f2 then f1 else f_or f1 f2

let f_or_simp_l l = List.fold_left f_or_simp f_false l

let f_implies_simp f1 f2 = match f1.f_node, f2.f_node with
  | Ftrue, _  -> f2
  | _, Ftrue  -> f2
  | Ffalse, _ -> f_not_simp f1
  | _, Ffalse -> f_not_simp f1
  | _, _      -> if f_equal f1 f2 then f_true else f_implies f1 f2

let f_iff_simp f1 f2 = match f1.f_node, f2.f_node with
  | Ftrue, _  -> f2
  | _, Ftrue  -> f1
  | Ffalse, _ -> f_not_simp f2
  | _, Ffalse -> f_not_simp f1
  | _, _      -> if f_equal f1 f2 then f_true else f_iff f1 f2

let f_binary_simp op = match op with
  | Fand     -> f_and_simp
  | For      -> f_or_simp
  | Fimplies -> f_implies_simp
  | Fiff     -> f_iff_simp

let t_if_simp f t1 t2 = match f.f_node with
  | Ftrue -> t1
  | Ffalse -> t2
  | _ -> if t_equal t1 t2 then t1 else t_if f t1 t2

let f_if_simp f1 f2 f3 = match f1.f_node, f2.f_node, f3.f_node with
  | Ftrue, _, _  -> f2
  | Ffalse, _, _ -> f3
  | _, Ftrue, _  -> f_implies_simp (f_not_simp f1) f3
  | _, Ffalse, _ -> f_and_simp (f_not_simp f1) f3
  | _, _, Ftrue  -> f_implies_simp f1 f2
  | _, _, Ffalse -> f_and_simp f1 f2
  | _, _, _      -> if f_equal f2 f3 then f2 else f_if f1 f2 f3

let f_let_simp t ((_,_,f) as bf) = match f.f_node with
  | Ftrue | Ffalse -> f | _ -> f_let t bf

let f_let_close_simp v t f = match f.f_node with
  | Ftrue | Ffalse -> f | _ -> f_let_close v t f

let f_quant_simp q ((_,_,_,f) as qf) = match f.f_node with
  | Ftrue | Ffalse -> f | _ -> f_quant q qf

let f_forall_simp = f_quant_simp Fforall
let f_exists_simp = f_quant_simp Fexists

let f_quant_close_simp q vl tl f = match f.f_node with
  | Ftrue | Ffalse -> f | _ -> f_quant_close q vl tl f

let f_forall_close_simp = f_quant_close_simp Fforall
let f_exists_close_simp = f_quant_close_simp Fexists

let f_equ_simp t1 t2 = if t_equal t1 t2 then f_true  else f_equ t1 t2
let f_neq_simp t1 t2 = if t_equal t1 t2 then f_false else f_neq t1 t2

let is_true_false f = match f.f_node with
  | Ftrue | Ffalse -> true | _  -> false

let f_forall_close_merge vs f =
  match f.f_node with
  | Fquant (Fforall, fq) ->
      let vs', trs, f = f_open_quant fq in
      f_forall_close (vs@vs') trs f
  | _ -> f_forall_close vs [] f

(* Could we add an optional argument which toggle
   the simplification to the other map? *)

let f_bound  fn b = let u,f,close = f_open_bound_cb  b in close u (fn f)
let f_branch fn b = let p,f,close = f_open_branch_cb b in close p (fn f)

let f_map_simp fnT fnF f = f_label_copy f (match f.f_node with
  | Fapp (p, [t1;t2]) when ls_equal p ps_equ -> f_equ_simp (fnT t1) (fnT t2)
  | Fapp (p, tl) -> f_app p (List.map fnT tl)
  | Fquant (q, b) ->
      let vl, tl, f1, close = f_open_quant_cb b in
      f_quant_simp q (close vl (tr_map fnT fnF tl) (fnF f1))
  | Fbinop (op, f1, f2) -> f_binary_simp op (fnF f1) (fnF f2)
  | Fnot f1 -> f_not_simp (fnF f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if_simp (fnF f1) (fnF f2) (fnF f3)
  | Flet (t, b) -> f_let_simp (fnT t) (f_bound fnF b)
  | Fcase (t, bl) -> f_case (fnT t) (List.map (f_branch fnF) bl))

let f_map_simp fnT = f_map_simp (protect fnT)

