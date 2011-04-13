(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

let vs_equal : vsymbol -> vsymbol -> bool = (==)

let vs_hash vs = id_hash vs.vs_name

let create_vsymbol name ty = {
  vs_name = id_register name;
  vs_ty   = ty;
}

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

let ls_equal : lsymbol -> lsymbol -> bool = (==)

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
  pat_ty   : ty;
  pat_tag  : int;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Por  of pattern * pattern
  | Pas  of pattern * vsymbol

let pat_equal : pattern -> pattern -> bool = (==)

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

let pat_wild ty = mk_pattern Pwild Svs.empty ty
let pat_var v   = mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty

let pat_as p v =
  let s = Svs.add_new v (DuplicateVar v) p.pat_vars in
  mk_pattern (Pas (p,v)) s v.vs_ty

let pat_or p q =
  if Svs.equal p.pat_vars q.pat_vars then
    mk_pattern (Por (p,q)) p.pat_vars p.pat_ty
  else
    let s = Mvs.union (fun _ _ _ -> None) p.pat_vars q.pat_vars in
    raise (UncoveredVar (Svs.choose s))

let pat_app f pl ty =
  let dup v () () = raise (DuplicateVar v) in
  let merge s p = Mvs.union dup s p.pat_vars in
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

let rec pat_gen_map fnT fnL m pat =
  let fn = pat_gen_map fnT fnL m in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (Mvs.find v m)
    | Papp (s, pl) -> pat_app (fnL s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (Mvs.find v m)
    | Por (p, q) -> pat_or (fn p) (fn q)

let rec pat_gen_fold fnT fnL acc pat =
  let fn acc p = pat_gen_fold fnT fnL acc p in
  let acc = fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild | Pvar _ -> acc
    | Papp (s, pl) -> List.fold_left fn (fnL acc s) pl
    | Por (p, q) -> fn (fn acc p) q
    | Pas (p, _) -> fn acc p

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
  t_node  : term_node;
  t_label : label list;
  t_loc   : Loc.position option;
  t_vars  : Svs.t;
  t_ty    : ty;
  t_tag   : int;
}

and fmla = {
  f_node  : fmla_node;
  f_label : label list;
  f_loc   : Loc.position option;
  f_vars  : Svs.t;
  f_tag   : int;
}

and term_node =
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
  bv_vars  : Svs.t;       (* free variables *)
  bv_subst : term Mvs.t   (* deferred substitution *)
}

and trigger = expr list

and expr =
  | Term of term
  | Fmla of fmla

(* term and fmla equality *)

let t_equal : term -> term -> bool = (==)
let f_equal : fmla -> fmla -> bool = (==)

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

let bnd_equal b1 b2 = Mvs.equal t_equal b1.bv_subst b2.bv_subst

let bnd_hash bv =
  let comb v t acc = Hashcons.combine2 (vs_hash v) (t_hash t) acc in
  Mvs.fold comb bv.bv_subst

let bnd_map fn bv = { bv with bv_subst = Mvs.map fn bv.bv_subst }
let bnd_fold fn acc bv = Mvs.fold (fun _ t a -> fn a t) bv.bv_subst acc

let bnd_map_fold fn acc bv =
  let acc,s = Mvs.mapi_fold (fun _ t a -> fn a t) bv.bv_subst acc in
  acc, { bv with bv_subst = s }

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
    ty_equal t1.t_ty t2.t_ty &&
    t_equal_node t1.t_node t2.t_node &&
    list_all2 (=) t1.t_label t2.t_label

  let t_hash_branch (p,b,t) =
    Hashcons.combine (pat_hash p) (bnd_hash b (t_hash t))

  let t_hash_bound (v,b,t) =
    Hashcons.combine (vs_hash v) (bnd_hash b (t_hash t))

  let f_hash_bound (v,b,f) =
    Hashcons.combine (vs_hash v) (bnd_hash b (f_hash f))

  let t_hash_node = function
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

  let add_t_vars s t = Svs.union s t.t_vars
  let add_b_vars s (_,b,_) = Svs.union s b.bv_vars

  let t_vars_node = function
    | Tvar v -> Svs.singleton v
    | Tconst _ -> Svs.empty
    | Tapp (_,tl) -> List.fold_left add_t_vars Svs.empty tl
    | Tif (f,t,e) -> add_t_vars (add_t_vars f.f_vars t) e
    | Tlet (t,bt) -> add_b_vars t.t_vars bt
    | Tcase (t,bl) -> List.fold_left add_b_vars t.t_vars bl
    | Teps (_,b,_) -> b.bv_vars

  let tag n t = { t with t_tag = n ; t_vars = t_vars_node t.t_node }

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

  let add_t_vars s t = Svs.union s t.t_vars
  let add_f_vars s f = Svs.union s f.f_vars
  let add_b_vars s (_,b,_) = Svs.union s b.bv_vars

  let f_vars_node = function
    | Fapp (_,tl) -> List.fold_left add_t_vars Svs.empty tl
    | Fquant (_,(_,b,_,_)) -> b.bv_vars
    | Fbinop (_,f1,f2) -> Svs.union f1.f_vars f2.f_vars
    | Fnot f -> f.f_vars
    | Ftrue | Ffalse -> Svs.empty
    | Fif (f1,f2,f3) -> add_f_vars (add_f_vars f1.f_vars f2) f3
    | Flet (t,bf) -> add_b_vars t.t_vars bf
    | Fcase (t,bl) -> List.fold_left add_b_vars t.t_vars bl

  let tag n f = { f with f_tag = n ; f_vars = f_vars_node f.f_node }

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
  t_node  = n;
  t_label = [];
  t_loc   = None;
  t_vars  = Svs.empty;
  t_ty    = ty;
  t_tag   = -1
}

let t_var v         = mk_term (Tvar v) v.vs_ty
let t_const c ty    = mk_term (Tconst c) ty
let t_int_const s   = mk_term (Tconst (ConstInt s)) Ty.ty_int
let t_real_const r  = mk_term (Tconst (ConstReal r)) Ty.ty_real
let t_app f tl ty   = mk_term (Tapp (f, tl)) ty
let t_if f t1 t2    = mk_term (Tif (f, t1, t2)) t2.t_ty
let t_let t1 bt ty  = mk_term (Tlet (t1, bt)) ty
let t_case t1 bl ty = mk_term (Tcase (t1, bl)) ty
let t_eps bf ty     = mk_term (Teps bf) ty

let t_label ?loc l t = Hsterm.hashcons { t with t_label = l; t_loc = loc }
let t_label_add  l t = Hsterm.hashcons { t with t_label = l :: t.t_label }

let t_label_copy { t_label = l; t_loc = p } t =
  if t.t_label = [] && t.t_loc = None && (l <> [] || p <> None)
  then t_label ?loc:p l t else t

(* hash-consing constructors for formulas *)

let mk_fmla n = Hsfmla.hashcons {
  f_node  = n;
  f_label = [];
  f_loc   = None;
  f_vars  = Svs.empty;
  f_tag   = -1
}

let f_app f tl        = mk_fmla (Fapp (f, tl))
let f_quant q qf      = mk_fmla (Fquant (q, qf))
let f_binary op f1 f2 = mk_fmla (Fbinop (op, f1, f2))
let f_not f           = mk_fmla (Fnot f)
let f_true            = mk_fmla (Ftrue)
let f_false           = mk_fmla (Ffalse)
let f_if f1 f2 f3     = mk_fmla (Fif (f1, f2, f3))
let f_let t bf        = mk_fmla (Flet (t, bf))
let f_case t bl       = mk_fmla (Fcase (t, bl))

let f_label ?loc l f = Hsfmla.hashcons { f with f_label = l; f_loc = loc }
let f_label_add  l f = Hsfmla.hashcons { f with f_label = l :: f.f_label }

let f_label_copy { f_label = l; f_loc = p } f =
  if f.f_label = [] && f.f_loc = None && (l <> [] || p <> None)
  then f_label ?loc:p l f else f

let f_and     = f_binary Fand
let f_or      = f_binary For
let f_implies = f_binary Fimplies
let f_iff     = f_binary Fiff

(* unsafe map *)

let bound_map fnT fnE (u,b,e) = (u, bnd_map fnT b, fnE e)

let t_map_unsafe fnT fnF t = t_label_copy t (match t.t_node with
  | Tvar _ | Tconst _ -> t
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
  | Tvar _ | Tconst _ -> acc
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
  | Tvar _ | Tconst _ ->
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

(* type-unsafe term substitution *)

let rec t_subst_unsafe m t =
  let t_subst t = t_subst_unsafe m t in
  let f_subst f = f_subst_unsafe m f in
  let b_subst (u,b,e) = (u, bv_subst_unsafe m b, e) in
  match t.t_node with
  | Tvar u ->
      Mvs.find_default u t m
  | Tlet (e, bt) ->
      t_label_copy t (t_let (t_subst e) (b_subst bt) t.t_ty)
  | Tcase (e, bl) ->
      let bl = List.map b_subst bl in
      t_label_copy t (t_case (t_subst e) bl t.t_ty)
  | Teps bf ->
      t_label_copy t (t_eps (b_subst bf) t.t_ty)
  | _ ->
      t_map_unsafe t_subst f_subst t

and f_subst_unsafe m f =
  let t_subst t = t_subst_unsafe m t in
  let f_subst f = f_subst_unsafe m f in
  let b_subst (u,b,e) = (u, bv_subst_unsafe m b, e) in
  match f.f_node with
  | Fquant (q, (vl,b,tl,f1)) ->
      let b = bv_subst_unsafe m b in
      f_label_copy f (f_quant q (vl,b,tl,f1))
  | Flet (e, bf) ->
      f_label_copy f (f_let (t_subst e) (b_subst bf))
  | Fcase (e, bl) ->
      let bl = List.map b_subst bl in
      f_label_copy f (f_case (t_subst e) bl)
  | _ ->
      f_map_unsafe t_subst f_subst f

and bv_subst_unsafe m b =
  (* restrict m to the variables free in b *)
  let m = Mvs.inter (fun _ t () -> Some t) m b.bv_vars in
  (* if m is empty, return early *)
  if Mvs.is_empty m then b else
  (* remove from b.bv_vars the variables replaced by m *)
  let s = Mvs.diff (fun _ () _ -> None) b.bv_vars m in
  (* add to b.bv_vars the free variables added by m *)
  let s = Mvs.fold (fun _ t -> Svs.union t.t_vars) m s in
  (* apply m to the terms in b.bv_subst *)
  let h = Mvs.map (t_subst_unsafe m) b.bv_subst in
  (* join m to b.bv_subst *)
  let h = Mvs.union (fun _ _ t -> Some t) m h in
  (* reconstruct b *)
  { bv_vars = s ; bv_subst = h }

let t_subst_unsafe m t =
  if Mvs.is_empty m then t else t_subst_unsafe m t

let f_subst_unsafe m f =
  if Mvs.is_empty m then f else f_subst_unsafe m f

(* close bindings *)

let bnd_new s = { bv_vars = s ; bv_subst = Mvs.empty }

let t_close_bound v t = (v, bnd_new (Svs.remove v t.t_vars), t)
let f_close_bound v f = (v, bnd_new (Svs.remove v f.f_vars), f)

let t_close_branch p t = (p, bnd_new (Svs.diff t.t_vars p.pat_vars), t)
let f_close_branch p f = (p, bnd_new (Svs.diff f.f_vars p.pat_vars), f)

let f_close_quant vl tl f =
  let del_v s v = Svs.remove v s in
  let add_t s t = Svs.union s t.t_vars in
  let add_f s f = Svs.union s f.f_vars in
  let s = tr_fold add_t add_f f.f_vars tl in
  let s = List.fold_left del_v s vl in
  (vl, bnd_new s, tl, f)

(* open bindings *)

let gen_fresh_vsymbol fnT v =
  create_vsymbol (id_clone v.vs_name) (fnT v.vs_ty)

let gen_vs_rename fnT h v =
  let u = gen_fresh_vsymbol fnT v in
  Mvs.add v (t_var u) h, u

let gen_vl_rename fnT h vl =
  Util.map_fold_left (gen_vs_rename fnT) h vl

let gen_pat_rename fnT fnL h p =
  let add_vs v () = gen_fresh_vsymbol fnT v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_gen_map fnT fnL m p in
  Mvs.union (fun _ _ t -> Some t) h (Mvs.map t_var m), p

let fresh_vsymbol = gen_fresh_vsymbol (fun ty -> ty)
let vs_rename = gen_vs_rename (fun ty -> ty)
let vl_rename = gen_vl_rename (fun ty -> ty)
let pat_rename = gen_pat_rename (fun ty -> ty) (fun ls -> ls)

let t_open_bound (v,b,t) =
  let m,v = vs_rename b.bv_subst v in
  v, t_subst_unsafe m t

let f_open_bound (v,b,f) =
  let m,v = vs_rename b.bv_subst v in
  v, f_subst_unsafe m f

let t_open_branch (p,b,t) =
  let m,p = pat_rename b.bv_subst p in
  p, t_subst_unsafe m t

let f_open_branch (p,b,f) =
  let m,p = pat_rename b.bv_subst p in
  p, f_subst_unsafe m f

let f_open_quant (vl,b,tl,f) =
  let m,vl = vl_rename b.bv_subst vl in
  let tl = tr_map (t_subst_unsafe m) (f_subst_unsafe m) tl in
  (vl, tl, f_subst_unsafe m f)

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
  let ts = ts_tuple n in
  let tl = List.map ty_var ts.ts_args in
  let ty = ty_app ts tl in
  create_fsymbol (id_fresh ("Tuple" ^ string_of_int n)) tl ty)

let is_fs_tuple fs = fs == fs_tuple (List.length fs.ls_args)

let t_tuple tl =
  let ty = ty_tuple (List.map (fun t -> t.t_ty) tl) in
  t_app (fs_tuple (List.length tl)) tl ty

(** Term library *)

(* generic map over types, symbols and variables *)

let gen_bnd_combine fn_t m { bv_subst = h } =
  Mvs.union (fun _ _ t -> Some t) m (Mvs.map fn_t h)

let rec t_gen_map fnT fnL m t =
  let fn_t = t_gen_map fnT fnL m in
  let fn_f = f_gen_map fnT fnL m in
  t_label_copy t (match t.t_node with
    | Tvar v ->
        let r = Mvs.find_default v t m in
        check_ty_equal (fnT t.t_ty) r.t_ty;
        r
    | Tconst _ ->
        t
    | Tapp (fs, tl) ->
        t_app (fnL fs) (List.map fn_t tl) (fnT t.t_ty)
    | Tif (f, t1, t2) ->
        t_if (fn_f f) (fn_t t1) (fn_t t2)
    | Tlet (t1, (u,b,t2)) ->
        let m = gen_bnd_combine fn_t m b in
        let m,v = gen_vs_rename fnT m u in
        t_let_close v (fn_t t1) (t_gen_map fnT fnL m t2)
    | Tcase (t1, bl) ->
        let fn_br (p,b,t2) =
          let m = gen_bnd_combine fn_t m b in
          let m,p = gen_pat_rename fnT fnL m p in
          t_close_branch p (t_gen_map fnT fnL m t2)
        in
        t_case (fn_t t1) (List.map fn_br bl)
    | Teps (u,b,f) ->
        let m = gen_bnd_combine fn_t m b in
        let m,v = gen_vs_rename fnT m u in
        t_eps_close v (f_gen_map fnT fnL m f))

and f_gen_map fnT fnL m f =
  let fn_t = t_gen_map fnT fnL m in
  let fn_f = f_gen_map fnT fnL m in
  f_label_copy f (match f.f_node with
    | Fapp (ps, tl) ->
        f_app (fnL ps) (List.map fn_t tl)
    | Fquant (q, (vl,b,tl,f1)) ->
        let m = gen_bnd_combine fn_t m b in
        let m,vl = gen_vl_rename fnT m vl in
        let fn_t = t_gen_map fnT fnL m in
        let fn_f = f_gen_map fnT fnL m in
        f_quant_close q vl (tr_map fn_t fn_f tl) (fn_f f1)
    | Fbinop (op, f1, f2) ->
        f_binary op (fn_f f1) (fn_f f2)
    | Fnot f1 ->
        f_not (fn_f f1)
    | Ftrue | Ffalse ->
        f
    | Fif (f1, f2, f3) ->
        f_if (fn_f f1) (fn_f f2) (fn_f f3)
    | Flet (t, (u,b,f1)) ->
        let m = gen_bnd_combine fn_t m b in
        let m,v = gen_vs_rename fnT m u in
        f_let_close v (fn_t t) (f_gen_map fnT fnL m f1)
    | Fcase (t, bl) ->
        let fn_br (p,b,f1) =
          let m = gen_bnd_combine fn_t m b in
          let m,p = gen_pat_rename fnT fnL m p in
          f_close_branch p (f_gen_map fnT fnL m f1)
        in
        f_case (fn_t t) (List.map fn_br bl))

let t_gen_map fnT fnL mapV t = t_gen_map (Wty.memoize 17 fnT) fnL mapV t
let f_gen_map fnT fnL mapV f = f_gen_map (Wty.memoize 17 fnT) fnL mapV f

(* map over type and logic symbols *)

let gen_mapV fnT = Mvs.mapi (fun v () -> t_var (gen_fresh_vsymbol fnT v))

let t_s_map fnT fnL t =
  let fnT = ty_s_map fnT in
  t_gen_map fnT fnL (gen_mapV fnT t.t_vars) t

let f_s_map fnT fnL f =
  let fnT = ty_s_map fnT in
  f_gen_map fnT fnL (gen_mapV fnT f.f_vars) f

(* simultaneous substitution into types and terms *)

let t_ty_subst mapT mapV t = t_gen_map (ty_inst mapT) (fun ls -> ls) mapV t
let f_ty_subst mapT mapV f = f_gen_map (ty_inst mapT) (fun ls -> ls) mapV f

(* fold over symbols *)

let rec t_gen_fold fnT fnL acc t =
  let fn_t = t_gen_fold fnT fnL in
  let fn_f = f_gen_fold fnT fnL in
  let acc = fnT acc t.t_ty in
  match t.t_node with
  | Tconst _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left fn_t (fnL acc f) tl
  | Tif (f, t1, t2) -> fn_t (fn_t (fn_f acc f) t1) t2
  | Tlet (t1, (_,b,t2)) -> fn_t (bnd_fold fn_t (fn_t acc t1) b) t2
  | Tcase (t1, bl) ->
      let branch acc (p,b,t) =
        fn_t (pat_gen_fold fnT fnL (bnd_fold fn_t acc b) p) t in
      List.fold_left branch (fn_t acc t1) bl
  | Teps (_,b,f) -> fn_f (bnd_fold fn_t acc b) f

and f_gen_fold fnT fnL acc f =
  let fn_t = t_gen_fold fnT fnL in
  let fn_f = f_gen_fold fnT fnL in
  match f.f_node with
  | Fapp (p, tl) -> List.fold_left fn_t (fnL acc p) tl
  | Fquant (_, (vl,b,tl,f1)) ->
      (* these variables (and their types) may never appear below *)
      let acc = List.fold_left (fun a v -> fnT a v.vs_ty) acc vl in
      fn_f (tr_fold fn_t fn_f (bnd_fold fn_t acc b) tl) f1
  | Fbinop (_, f1, f2) -> fn_f (fn_f acc f1) f2
  | Fnot f1 -> fn_f acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fn_f (fn_f (fn_f acc f1) f2) f3
  | Flet (t, (_,b,f1)) -> fn_f (bnd_fold fn_t (fn_t acc t) b) f1
  | Fcase (t, bl) ->
      let branch acc (p,b,f) =
        fn_f (pat_gen_fold fnT fnL (bnd_fold fn_t acc b) p) f in
      List.fold_left branch (fn_t acc t) bl

let t_s_fold fnT fnL acc t = t_gen_fold (ty_s_fold fnT) fnL acc t
let f_s_fold fnT fnL acc f = f_gen_fold (ty_s_fold fnT) fnL acc f

let t_s_all prT prL t =
  try t_s_fold (all_fn prT) (all_fn prL) true t with FoldSkip -> false

let f_s_all prT prL f =
  try f_s_fold (all_fn prT) (all_fn prL) true f with FoldSkip -> false

let t_s_any prT prL t =
  try t_s_fold (any_fn prT) (any_fn prL) false t with FoldSkip -> true

let f_s_any prT prL f =
  try f_s_fold (any_fn prT) (any_fn prL) false f with FoldSkip -> true

(* fold over types in terms and formulas *)

let t_ty_fold fn acc t = t_gen_fold fn Util.const acc t
let f_ty_fold fn acc f = f_gen_fold fn Util.const acc f

(* fold over applications in terms and formulas (but not in patterns!) *)

let rec t_app_fold fn acc t =
  let acc = t_fold_unsafe (t_app_fold fn) (f_app_fold fn) acc t in
  match t.t_node with
    | Tapp (ls,tl) -> fn acc ls (List.map (fun t -> t.t_ty) tl) (Some t.t_ty)
    | _ -> acc

and f_app_fold fn acc f =
  let acc = f_fold_unsafe (t_app_fold fn) (f_app_fold fn) acc f in
  match f.f_node with
    | Fapp (ls,tl) -> fn acc ls (List.map (fun t -> t.t_ty) tl) None
    | _ -> acc

(* free type variables *)

let t_ty_freevars s t = t_gen_fold ty_freevars Util.const s t
let f_ty_freevars s f = f_gen_fold ty_freevars Util.const s f

(* safe opening map *)

let t_bound  fn b = let u,t,close = t_open_bound_cb  b in close u (fn t)
let f_bound  fn b = let u,f,close = f_open_bound_cb  b in close u (fn f)
let t_branch fn b = let p,t,close = t_open_branch_cb b in close p (fn t)
let f_branch fn b = let p,f,close = f_open_branch_cb b in close p (fn f)

let t_map fnT fnF t = match t.t_node with
  | Tlet (t1, b) ->
      t_label_copy t (t_let (fnT t1) (t_bound fnT b))
  | Tcase (t1, bl) ->
      t_label_copy t (t_case (fnT t1) (List.map (t_branch fnT) bl))
  | Teps b ->
      t_label_copy t (t_eps (f_bound fnF b))
  | _ ->
      t_map_unsafe fnT fnF t

let f_map fnT fnF f = match f.f_node with
  | Fquant (q, b) ->
      let vl, tl, f1, close = f_open_quant_cb b in
      f_label_copy f (f_quant q (close vl (tr_map fnT fnF tl) (fnF f1)))
  | Flet (t, b) ->
      f_label_copy f (f_let (fnT t) (f_bound fnF b))
  | Fcase (t, bl) ->
      f_label_copy f (f_case (fnT t) (List.map (f_branch fnF) bl))
  | _ ->
      f_map_unsafe fnT fnF f

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

let e_map_cont fnT fnF contE = function
  | Term t -> fnT (fun t -> contE (Term t)) t
  | Fmla f -> fnF (fun f -> contE (Fmla f)) f

let tr_map_cont fnT fnF =
  list_map_cont (list_map_cont (e_map_cont fnT fnF))

let t_map_cont fnT fnF contT t =
  let contT e = contT (t_label_copy t e) in
  match t.t_node with
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

let protect_vs fn v =
  let res = fn v in
  check_ty_equal v.vs_ty res.t_ty;
  res

let t_v_map fn t =
  let m = Mvs.mapi (fun v () -> protect_vs fn v) t.t_vars in
  t_subst_unsafe m t

let f_v_map fn f =
  let m = Mvs.mapi (fun v () -> protect_vs fn v) f.f_vars in
  f_subst_unsafe m f

let t_v_fold fn acc t = Svs.fold (fun v a -> fn a v) t.t_vars acc
let f_v_fold fn acc f = Svs.fold (fun v a -> fn a v) f.f_vars acc

let t_v_all pr t = Svs.for_all pr t.t_vars
let f_v_all pr f = Svs.for_all pr f.f_vars
let t_v_any pr t = Svs.exists  pr t.t_vars
let f_v_any pr f = Svs.exists  pr f.f_vars

(* looks for occurrence of a variable from set [s] in a term [t] *)

let t_occurs s t = not (Svs.is_empty (Svs.inter s t.t_vars))
let f_occurs s f = not (Svs.is_empty (Svs.inter s f.f_vars))

let t_occurs_single v t = Svs.mem v t.t_vars
let f_occurs_single v f = Svs.mem v f.f_vars

(* replaces variables with terms in term [t] using map [m] *)

let t_subst m t =
  Mvs.iter (fun v t -> check_ty_equal v.vs_ty t.t_ty) m;
  t_subst_unsafe m t

let f_subst m f =
  Mvs.iter (fun v t -> check_ty_equal v.vs_ty t.t_ty) m;
  f_subst_unsafe m f

let t_subst_single v t1 t = t_subst (Mvs.singleton v t1) t
let f_subst_single v t1 f = f_subst (Mvs.singleton v t1) f

(* set of free variables *)

let t_freevars s t = Svs.union s t.t_vars
let f_freevars s f = Svs.union s f.f_vars

(* alpha-equality *)

let vs_rename_alpha c h vs = incr c; Mvs.add vs !c h

let vl_rename_alpha c h vl = List.fold_left (vs_rename_alpha c) h vl

let rec pat_rename_alpha c h p = match p.pat_node with
  | Pvar v -> vs_rename_alpha c h v
  | Pas (p, v) -> pat_rename_alpha c (vs_rename_alpha c h v) p
  | Por (p, _) -> pat_rename_alpha c h p
  | _ -> pat_fold (pat_rename_alpha c) h p

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

let rec t_equal_alpha c1 c2 m1 m2 t1 t2 =
  t_equal t1 t2 || ty_equal t1.t_ty t2.t_ty &&
  let t_eq = t_equal_alpha c1 c2 m1 m2 in
  let f_eq = f_equal_alpha c1 c2 m1 m2 in
  match t1.t_node, t2.t_node with
    | Tvar v1, Tvar v2 when Mvs.mem v1 m1 ->
        Mvs.mem v2 m2 && Mvs.find v1 m1 = Mvs.find v2 m2
    | Tvar v1, Tvar v2 when not (Mvs.mem v2 m2) ->
        vs_equal v1 v2
    | Tconst c1, Tconst c2 ->
        c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_eq l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
        f_eq f1 f2 && t_eq t1 t2 && t_eq e1 e2
    | Tlet (t1,b1), Tlet (t2,b2) ->
        t_eq t1 t2 &&
        let u1,e1 = t_open_bound b1 in
        let u2,e2 = t_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        t_equal_alpha c1 c2 m1 m2 e1 e2
    | Tcase (t1,bl1), Tcase (t2,bl2) ->
        t_eq t1 t2 &&
        let br_eq ((p1,_,_) as b1) ((p2,_,_) as b2) =
          pat_equal_alpha p1 p2 &&
          let p1,e1 = t_open_branch b1 in
          let p2,e2 = t_open_branch b2 in
          let m1 = pat_rename_alpha c1 m1 p1 in
          let m2 = pat_rename_alpha c2 m2 p2 in
          t_equal_alpha c1 c2 m1 m2 e1 e2
        in
        list_all2 br_eq bl1 bl2
    | Teps b1, Teps b2 ->
        let u1,e1 = f_open_bound b1 in
        let u2,e2 = f_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        f_equal_alpha c1 c2 m1 m2 e1 e2
    | _ -> false

and f_equal_alpha c1 c2 m1 m2 f1 f2 =
  f_equal f1 f2 ||
  let t_eq = t_equal_alpha c1 c2 m1 m2 in
  let f_eq = f_equal_alpha c1 c2 m1 m2 in
  match f1.f_node, f2.f_node with
    | Fapp (s1,l1), Fapp (s2,l2) ->
        ls_equal s1 s2 && List.for_all2 t_eq l1 l2
    | Fquant (q1,((vl1,_,_,_) as b1)), Fquant (q2,((vl2,_,_,_) as b2)) ->
        q1 = q2 &&
        list_all2 (fun v1 v2 -> ty_equal v1.vs_ty v2.vs_ty) vl1 vl2 &&
        let vl1,_,e1 = f_open_quant b1 in
        let vl2,_,e2 = f_open_quant b2 in
        let m1 = vl_rename_alpha c1 m1 vl1 in
        let m2 = vl_rename_alpha c2 m2 vl2 in
        f_equal_alpha c1 c2 m1 m2 e1 e2
    | Fbinop (a,f1,g1), Fbinop (b,f2,g2) ->
        a = b && f_eq f1 f2 && f_eq g1 g2
    | Fnot f1, Fnot f2 ->
        f_eq f1 f2
    | Ftrue, Ftrue | Ffalse, Ffalse ->
        true
    | Fif (f1,g1,h1), Fif (f2,g2,h2) ->
        f_eq f1 f2 && f_eq g1 g2 && f_eq h1 h2
    | Flet (t1,b1), Flet (t2,b2) ->
        t_eq t1 t2 &&
        let u1,e1 = f_open_bound b1 in
        let u2,e2 = f_open_bound b2 in
        let m1 = vs_rename_alpha c1 m1 u1 in
        let m2 = vs_rename_alpha c2 m2 u2 in
        f_equal_alpha c1 c2 m1 m2 e1 e2
    | Fcase (t1,bl1), Fcase (t2,bl2) ->
        t_eq t1 t2 &&
        let br_eq ((p1,_,_) as b1) ((p2,_,_) as b2) =
          pat_equal_alpha p1 p2 &&
          let p1,e1 = f_open_branch b1 in
          let p2,e2 = f_open_branch b2 in
          let m1 = pat_rename_alpha c1 m1 p1 in
          let m2 = pat_rename_alpha c2 m2 p2 in
          f_equal_alpha c1 c2 m1 m2 e1 e2
        in
        list_all2 br_eq bl1 bl2
    | _ -> false

let t_equal_alpha = t_equal_alpha (ref (-1)) (ref (-1)) Mvs.empty Mvs.empty
let f_equal_alpha = f_equal_alpha (ref (-1)) (ref (-1)) Mvs.empty Mvs.empty

(* hash modulo alpha *)

let rec pat_hash_alpha p =
  match p.pat_node with
  | Pwild -> 0
  | Pvar _ -> 1
  | Papp (f, l) ->
      let acc = Hashcons.combine 2 (ls_hash f) in
      Hashcons.combine_list pat_hash_alpha acc l
  | Pas (p, _) -> Hashcons.combine 3 (pat_hash_alpha p)
  | Por (p, q) ->
      Hashcons.combine
        (Hashcons.combine 4 (pat_hash_alpha p)) (pat_hash_alpha q)

let rec t_hash_alpha c m t =
  let fn_t = t_hash_alpha c m in
  let fn_f = f_hash_alpha c m in
  match t.t_node with
  | Tvar v ->
      Hashcons.combine 0 (Mvs.find_default v (vs_hash v) m)
  | Tconst c ->
      Hashcons.combine 1 (Hashtbl.hash c)
  | Tapp (s,l) ->
      let acc = Hashcons.combine 2 (ls_hash s) in
      Hashcons.combine_list fn_t acc l
  | Tif (f,t1,t2) ->
      Hashcons.combine3 3 (fn_f f) (fn_t t1) (fn_t t2)
  | Tlet (t1,b) ->
      let u,t2 = t_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine2 4 (fn_t t1) (t_hash_alpha c m t2)
  | Tcase (t1,bl) ->
      let hash_br b =
        let p,t2 = t_open_branch b in
        let m = pat_rename_alpha c m p in
        t_hash_alpha c m t2
      in
      let acc = Hashcons.combine 5 (fn_t t1) in
      Hashcons.combine_list hash_br acc bl
  | Teps b ->
      let u,f = f_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine 6 (f_hash_alpha c m f)

and f_hash_alpha c m f =
  let fn_t = t_hash_alpha c m in
  let fn_f = f_hash_alpha c m in
  match f.f_node with
  | Fapp (s,l) ->
      let acc = Hashcons.combine 0 (ls_hash s) in
      Hashcons.combine_list fn_t acc l
  | Fquant (q,b) ->
      let vl,_,f1 = f_open_quant b in
      let m = vl_rename_alpha c m vl in
      let hq = match q with Fforall -> 1 | Fexists -> 2 in
      Hashcons.combine2 1 hq (f_hash_alpha c m f1)
  | Fbinop (o,f,g) ->
      let ho = match o with
        | Fand -> 3 | For -> 4 | Fimplies -> 5 | Fiff -> 7
      in
      Hashcons.combine3 2 ho (fn_f f) (fn_f g)
  | Fnot f ->
      Hashcons.combine 3 (fn_f f)
  | Ftrue -> 4
  | Ffalse -> 5
  | Fif (f1,f2,f3) ->
      Hashcons.combine3 6 (fn_f f1) (fn_f f2) (fn_f f3)
  | Flet (t,b) ->
      let u,f1 = f_open_bound b in
      let m = vs_rename_alpha c m u in
      Hashcons.combine2 7 (fn_t t) (f_hash_alpha c m f1)
  | Fcase (t,bl) ->
      let hash_br b =
        let p,f1 = f_open_branch b in
        let m = pat_rename_alpha c m p in
        f_hash_alpha c m f1
      in
      let acc = Hashcons.combine 8 (fn_t t) in
      Hashcons.combine_list hash_br acc bl

let t_hash_alpha = t_hash_alpha (ref (-1)) Mvs.empty
let f_hash_alpha = f_hash_alpha (ref (-1)) Mvs.empty

module Hterm_alpha = Hashtbl.Make (struct
  type t = term
  let equal = t_equal_alpha
  let hash = t_hash_alpha
end)

module Hfmla_alpha = Hashtbl.Make (struct
  type t = fmla
  let equal = f_equal_alpha
  let hash = f_hash_alpha
end)

(* binder-free term/formula matching *)

exception NoMatch

let rec t_match s t1 t2 =
  if t_equal t1 t2 then s else
  if not (ty_equal t1.t_ty t2.t_ty) then raise NoMatch else
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
  | Ffalse, _ -> f1 (* more efficient than f_false *)
  | _, Ffalse -> f2 (* more efficient than f_false *)
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
  | Ffalse, _ -> f_true
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

let t_let_simp e ((v,_,t) as bt) = match e.t_node with
  | _ when not (Svs.mem v t.t_vars) -> snd (t_open_bound bt)
  | Tvar _ -> let v,t = t_open_bound bt in t_subst_single v e t
  | _ -> t_let e bt

let f_let_simp e ((v,_,f) as bf) = match e.t_node with
  | _ when not (Svs.mem v f.f_vars) -> snd (f_open_bound bf)
  | Tvar _ -> let v,f = f_open_bound bf in f_subst_single v e f
  | _ -> f_let e bf

let t_let_close_simp v e t = match e.t_node with
  | _ when not (Svs.mem v t.t_vars) -> t
  | Tvar _ -> t_subst_single v e t
  | _ -> t_let_close v e t

let f_let_close_simp v e f = match e.t_node with
  | _ when not (Svs.mem v f.f_vars) -> f
  | Tvar _ -> f_subst_single v e f
  | _ -> f_let_close v e f

let vl_filter f vl =
  List.filter (fun v -> Svs.mem v f.f_vars) vl

let tr_filter f tl =
  let e_vars = e_apply (fun t -> t.t_vars) (fun f -> f.f_vars) in
  List.filter (List.for_all (fun e -> Svs.subset (e_vars e) f.f_vars)) tl

let f_quant_simp q ((vl,_,_,f) as qf) =
  if List.for_all (fun v -> Svs.mem v f.f_vars) vl then
    f_quant q qf
  else
    let vl,tl,f = f_open_quant qf in
    let vl = vl_filter f vl in if vl = [] then f else
    f_quant_close q vl (tr_filter f tl) f

let f_quant_close_simp q vl tl f =
  if List.for_all (fun v -> Svs.mem v f.f_vars) vl then
    f_quant_close q vl tl f
  else
    let vl = vl_filter f vl in if vl = [] then f else
    f_quant_close q vl (tr_filter f tl) f

let f_forall_simp = f_quant_simp Fforall
let f_exists_simp = f_quant_simp Fexists

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

