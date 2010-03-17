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

module Vsym = struct
  type t = vsymbol
  let equal = (==)
  let hash vs = vs.vs_name.id_tag
  let compare vs1 vs2 =
    Pervasives.compare vs1.vs_name.id_tag vs2.vs_name.id_tag
end

module Mvs = Map.Make(Vsym)
module Svs = Set.Make(Vsym)
module Hvs = Hashtbl.Make(Vsym)

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
  ls_constr : bool;
}

module Lsym = struct
  type t = lsymbol
  let equal = (==)
  let hash fs = fs.ls_name.id_tag
  let compare fs1 fs2 =
    Pervasives.compare fs1.ls_name.id_tag fs2.ls_name.id_tag
end
module Sls = Set.Make(Lsym)
module Mls = Map.Make(Lsym)
module Hls = Hashtbl.Make(Lsym)

let create_lsymbol name args value constr = {
  ls_name   = id_register name;
  ls_args   = args;
  ls_value  = value;
  ls_constr = constr;
}

let create_fsymbol nm al vl = create_lsymbol nm al (Some vl) false
let create_fconstr nm al vl = create_lsymbol nm al (Some vl) true
let create_psymbol nm al    = create_lsymbol nm al None false

(** Patterns *)

type pattern = {
  pat_node : pattern_node;
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Pas of pattern * vsymbol

module Hpat = struct

  type t = pattern

  let equal_node p1 p2 = match p1, p2 with
    | Pwild, Pwild -> true
    | Pvar v1, Pvar v2 -> v1 == v2
    | Papp (s1, l1), Papp (s2, l2) -> s1 == s2 && List.for_all2 (==) l1 l2
    | Pas (p1, n1), Pas (p2, n2) -> p1 == p2 && n1 == n2
    | _ -> false

  let equal p1 p2 =
    equal_node p1.pat_node p2.pat_node && p1.pat_ty == p2.pat_ty

  let hash_pattern p = p.pat_tag

  let hash_node = function
    | Pwild -> 0
    | Pvar v -> v.vs_name.id_tag
    | Papp (s, pl) -> Hashcons.combine_list hash_pattern s.ls_name.id_tag pl
    | Pas (p, v) -> Hashcons.combine (hash_pattern p) v.vs_name.id_tag

  let hash p = Hashcons.combine (hash_node p.pat_node) p.pat_ty.ty_tag

  let tag n p = { p with pat_tag = n }

end
module Hp = Hashcons.Make(Hpat)

(* h-consing constructors for patterns *)

let mk_pattern n ty = { pat_node = n; pat_ty = ty; pat_tag = -1 }
let pat_wild ty = Hp.hashcons (mk_pattern Pwild ty)
let pat_var v = Hp.hashcons (mk_pattern (Pvar v) v.vs_ty)
let pat_app f pl ty = Hp.hashcons (mk_pattern (Papp (f, pl)) ty)
let pat_as p v = Hp.hashcons (mk_pattern (Pas (p, v)) p.pat_ty)

(* generic traversal functions *)

let pat_map fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as (fn p) v

let protect fn pat =
  let res = fn pat in
  if res.pat_ty != pat.pat_ty then raise TypeMismatch;
  res

let pat_map fn = pat_map (protect fn)

let pat_fold fn acc pat = match pat.pat_node with
  | Pwild | Pvar _ -> acc
  | Papp (_, pl) -> List.fold_left fn acc pl
  | Pas (p, _) -> fn acc p

let pat_all pr pat =
  try pat_fold (all_fn pr) true pat with FoldSkip -> false

let pat_any pr pat =
  try pat_fold (any_fn pr) false pat with FoldSkip -> true

(* smart constructors for patterns *)

exception BadArity
exception ConstructorExpected of lsymbol
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol

let pat_app fs pl ty =
  if not fs.ls_constr then raise (ConstructorExpected fs);
  let s = match fs.ls_value with
    | Some vty -> Ty.matching Mtv.empty vty ty
    | None -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty p = Ty.matching s ty p.pat_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args pl
          with Invalid_argument _ -> raise BadArity);
  pat_app fs pl ty

let pat_as p v =
  if p.pat_ty != v.vs_ty then raise TypeMismatch;
  pat_as p v

(* symbol-wise map/fold *)

let rec pat_s_map fnT fnV fnL pat =
  let fn p = pat_s_map fnT fnV fnL p in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (fnV v ty)
    | Papp (s, pl) -> pat_app (fnL s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (fnV v ty)

let rec pat_s_fold fnT fnL acc pat =
  let fn acc p = pat_s_fold fnT fnL acc p in
  let acc = ty_s_fold fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild | Pvar _ -> acc
    | Papp (s, pl) -> List.fold_left fn (fnL acc s) pl
    | Pas (p, _) -> fn acc p

(** Terms and formulas *)

type label = string

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

and term_bound = vsymbol * term

and fmla_bound = vsymbol * fmla

and fmla_quant = vsymbol list * int * trigger list * fmla

and term_branch = pattern * int * term

and fmla_branch = pattern * int * fmla

and expr =
  | Term of term
  | Fmla of fmla

and trigger = expr list

(* expr and trigger traversal *)

let e_map fnT fnF = function Term t -> Term (fnT t) | Fmla f -> Fmla (fnF f)
let e_fold fnT fnF acc = function Term t -> fnT acc t | Fmla f -> fnF acc f
let e_apply fnT fnF = function Term t -> fnT t | Fmla f -> fnF f

let tr_map fnT fnF = List.map (List.map (e_map fnT fnF))
let tr_fold fnT fnF = List.fold_left (List.fold_left (e_fold fnT fnF))

module T = struct

  type t = term

  let t_eq_branch (p1, _, t1) (p2, _, t2) = p1 == p2 && t1 == t2

  let t_eq_bound (v1, t1) (v2, t2) = v1 == v2 && t1 == t2

  let f_eq_bound (v1, f1) (v2, f2) = v1 == v2 && f1 == f2

  let t_equal_node t1 t2 = match t1, t2 with
    | Tbvar x1, Tbvar x2 -> x1 == x2
    | Tvar v1, Tvar v2 -> v1 == v2
    | Tconst c1, Tconst c2 -> c1 = c2
    | Tapp (s1, l1), Tapp (s2, l2) -> s1 == s2 && List.for_all2 (==) l1 l2
    | Tlet (t1, b1), Tlet (t2, b2) -> t1 == t2 && t_eq_bound b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t1 == t2 &&
        (try List.for_all2 t_eq_branch l1 l2
        with Invalid_argument _ -> false)
    | Teps f1, Teps f2 -> f_eq_bound f1 f2
    | _ -> false

  let equal t1 t2 =
    t_equal_node t1.t_node t2.t_node &&
    t1.t_ty == t2.t_ty &&
    try List.for_all2 (=) t1.t_label t2.t_label
    with Invalid_argument _ -> false

  let t_hash_branch (p, _, t) = Hashcons.combine p.pat_tag t.t_tag

  let t_hash_bound (v, t) = Hashcons.combine v.vs_name.id_tag t.t_tag

  let f_hash_bound (v, f) = Hashcons.combine v.vs_name.id_tag f.f_tag

  let t_hash t = t.t_tag

  let t_hash_node = function
    | Tbvar n -> n
    | Tvar v -> v.vs_name.id_tag
    | Tconst c -> Hashtbl.hash c
    | Tapp (f, tl) -> Hashcons.combine_list t_hash (f.ls_name.id_tag) tl
    | Tlet (t, bt) -> Hashcons.combine t.t_tag (t_hash_bound bt)
    | Tcase (t, bl) -> Hashcons.combine_list t_hash_branch t.t_tag bl
    | Teps f -> f_hash_bound f

  let hash t =
    Hashcons.combine (t_hash_node t.t_node)
      (Hashcons.combine_list Hashtbl.hash t.t_ty.ty_tag t.t_label)

  let tag n t = { t with t_tag = n }

  let compare t1 t2 = Pervasives.compare t1.t_tag t2.t_tag

end
module Hterm = Hashcons.Make(T)
module Mterm = Map.Make(T)
module Sterm = Set.Make(T)

module F = struct

  type t = fmla

  let f_eq_branch (p1, _, f1) (p2, _, f2) = p1 == p2 && f1 == f2

  let f_eq_bound (v1, f1) (v2, f2) = v1 == v2 && f1 == f2

  let tr_eq tr1 tr2 = match tr1,tr2 with
    | Term t1, Term t2 -> t1 == t2
    | Fmla f1, Fmla f2 -> f1 == f2
    | _ -> false

  let f_eq_quant (vl1, n1, tl1, f1) (vl2, n2, tl2, f2) =
    n1 == n2 && f1 == f2 && List.for_all2 (==) vl1 vl2 &&
    try List.for_all2 (List.for_all2 tr_eq) tl1 tl2
    with Invalid_argument _ -> false

  let f_equal_node f1 f2 = match f1, f2 with
    | Fapp (s1, l1), Fapp (s2, l2) ->
        s1 == s2 && List.for_all2 (==) l1 l2
    | Fquant (q1, b1), Fquant (q2, b2) ->
        q1 == q2 && f_eq_quant b1 b2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) ->
        op1 == op2 && f1 == f2 && g1 == g2
    | Fnot f1, Fnot f2 ->
        f1 == f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        true
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
        f1 == f2 && g1 == g2 && h1 == h2
    | Flet (t1, b1), Flet (t2, b2) ->
        t1 == t2 && f_eq_bound b1 b2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t1 == t2 &&
        (try List.for_all2 f_eq_branch l1 l2
        with Invalid_argument _ -> false)
    | _ ->
        false

  let equal f1 f2 =
    f_equal_node f1.f_node f2.f_node &&
    try List.for_all2 (=) f1.f_label f2.f_label
    with Invalid_argument _ -> false

  let v_hash v = v.vs_name.id_tag

  let t_hash t = t.t_tag

  let f_hash f = f.f_tag

  let f_hash_branch (p, _, f) = Hashcons.combine p.pat_tag f.f_tag

  let f_hash_bound (v, f) = Hashcons.combine v.vs_name.id_tag f.f_tag

  let tr_hash = function Term t -> t.t_tag | Fmla f -> f.f_tag

  let f_hash_quant (vl, _, tl, f) =
    let h = Hashcons.combine_list v_hash f.f_tag vl in
    List.fold_left (Hashcons.combine_list tr_hash) h tl

  let f_hash_node = function
    | Fapp (p, tl) -> Hashcons.combine_list t_hash p.ls_name.id_tag tl
    | Fquant (q, bf) -> Hashcons.combine (Hashtbl.hash q) (f_hash_quant bf)
    | Fbinop (op, f1, f2) ->
        Hashcons.combine2 (Hashtbl.hash op) f1.f_tag f2.f_tag
    | Fnot f -> Hashcons.combine 1 f.f_tag
    | Ftrue -> 0
    | Ffalse -> 1
    | Fif (f1, f2, f3) -> Hashcons.combine2 f1.f_tag f2.f_tag f3.f_tag
    | Flet (t, bf) -> Hashcons.combine t.t_tag (f_hash_bound bf)
    | Fcase (t, bl) -> Hashcons.combine_list f_hash_branch t.t_tag bl

  let hash f =
    Hashcons.combine_list Hashtbl.hash (f_hash_node f.f_node) f.f_label

  let tag n f = { f with f_tag = n }

  let compare f1 f2 = Pervasives.compare f1.f_tag f2.f_tag

end
module Hfmla = Hashcons.Make(F)
module Mfmla = Map.Make(F)
module Sfmla = Set.Make(F)

(* hash-consing constructors for terms *)

let mk_term n ty = { t_node = n; t_label = []; t_ty = ty; t_tag = -1 }
let t_bvar n ty = Hterm.hashcons (mk_term (Tbvar n) ty)
let t_var v = Hterm.hashcons (mk_term (Tvar v) v.vs_ty)
let t_const c ty = Hterm.hashcons (mk_term (Tconst c) ty)
let t_app f tl ty = Hterm.hashcons (mk_term (Tapp (f, tl)) ty)
let t_let v t1 t2 = Hterm.hashcons (mk_term (Tlet (t1, (v, t2))) t2.t_ty)
let t_case t bl ty = Hterm.hashcons (mk_term (Tcase (t, bl)) ty)
let t_eps u f = Hterm.hashcons (mk_term (Teps (u, f)) u.vs_ty)

let t_label     l t = Hterm.hashcons { t with t_label = l }
let t_label_add l t = Hterm.hashcons { t with t_label = l :: t.t_label }
let t_label_copy { t_label = l } t = if l == [] then t else t_label l t

let t_app_unsafe = t_app

(* hash-consing constructors for formulas *)

let mk_fmla n = { f_node = n; f_label = []; f_tag = -1 }
let f_app f tl = Hfmla.hashcons (mk_fmla (Fapp (f, tl)))
let f_quant q ul n tl f = Hfmla.hashcons (mk_fmla (Fquant (q, (ul,n,tl,f))))

let f_binary op f1 f2 = Hfmla.hashcons (mk_fmla (Fbinop (op, f1, f2)))
let f_and = f_binary Fand
let f_or = f_binary For
let f_implies = f_binary Fimplies
let f_iff = f_binary Fiff

let f_not f = Hfmla.hashcons (mk_fmla (Fnot f))
let f_true = Hfmla.hashcons (mk_fmla Ftrue)
let f_false = Hfmla.hashcons (mk_fmla Ffalse)
let f_if f1 f2 f3 = Hfmla.hashcons (mk_fmla (Fif (f1, f2, f3)))
let f_let v t f = Hfmla.hashcons (mk_fmla (Flet (t, (v, f))))
let f_case t bl = Hfmla.hashcons (mk_fmla (Fcase (t, bl)))

let f_label     l f = Hfmla.hashcons { f with f_label = l }
let f_label_add l f = Hfmla.hashcons { f with f_label = l :: f.f_label }
let f_label_copy { f_label = l } f = if l == [] then f else f_label l f

(* built-in symbols *)

let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix =") [v; v]

let ps_neq =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix <>") [v; v]

let f_equ t1 t2 = f_app ps_equ [t1; t2]
let f_neq t1 t2 = f_app ps_neq [t1; t2]

let f_app p tl =
  if p == ps_neq then f_not (f_app ps_equ tl) else f_app p tl

let f_app_unsafe = f_app

(* unsafe map with level *)

exception UnboundIndex

let brlvl fn lvl (pat, nv, t) = (pat, nv, fn (lvl + nv) t)

let t_map_unsafe fnT fnF lvl t = t_label_copy t (match t.t_node with
  | Tbvar n when n >= lvl -> raise UnboundIndex
  | Tbvar _ | Tvar _ | Tconst _ -> t
  | Tapp (f, tl) -> t_app f (List.map (fnT lvl) tl) t.t_ty
  | Tlet (t1, (u, t2)) -> t_let u (fnT lvl t1) (fnT (lvl + 1) t2)
  | Tcase (t1, bl) -> t_case (fnT lvl t1) (List.map (brlvl fnT lvl) bl) t.t_ty
  | Teps (u, f) -> t_eps u (fnF (lvl + 1) f))

let f_map_unsafe fnT fnF lvl f = f_label_copy f (match f.f_node with
  | Fapp (p, tl) -> f_app p (List.map (fnT lvl) tl)
  | Fquant (q, (vl, nv, tl, f1)) -> let lvl = lvl + nv in
      f_quant q vl nv (tr_map (fnT lvl) (fnF lvl) tl) (fnF lvl f1)
  | Fbinop (op, f1, f2) -> f_binary op (fnF lvl f1) (fnF lvl f2)
  | Fnot f1 -> f_not (fnF lvl f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF lvl f1) (fnF lvl f2) (fnF lvl f3)
  | Flet (t, (u, f1)) -> f_let u (fnT lvl t) (fnF (lvl + 1) f1)
  | Fcase (t, bl) -> f_case (fnT lvl t) (List.map (brlvl fnF lvl) bl))

let protect fn lvl t =
  let res = fn lvl t in
  if res.t_ty != t.t_ty then raise TypeMismatch;
  res

let t_map_unsafe fnT = t_map_unsafe (protect fnT)
let f_map_unsafe fnT = f_map_unsafe (protect fnT)

(* unsafe fold with level *)

let brlvl fn lvl acc (_, nv, t) = fn (lvl + nv) acc t

let t_fold_unsafe fnT fnF lvl acc t = match t.t_node with
  | Tbvar n when n >= lvl -> raise UnboundIndex
  | Tbvar _ | Tvar _ | Tconst _ -> acc
  | Tapp (f, tl) -> List.fold_left (fnT lvl) acc tl
  | Tlet (t1, (u, t2)) -> fnT (lvl + 1) (fnT lvl acc t1) t2
  | Tcase (t1, bl) -> List.fold_left (brlvl fnT lvl) (fnT lvl acc t1) bl
  | Teps (u, f) -> fnF (lvl + 1) acc f

let f_fold_unsafe fnT fnF lvl acc f = match f.f_node with
  | Fapp (p, tl) -> List.fold_left (fnT lvl) acc tl
  | Fquant (q, (vl, nv, tl, f1)) -> let lvl = lvl + nv in
      tr_fold (fnT lvl) (fnF lvl) (fnF lvl acc f1) tl
  | Fbinop (op, f1, f2) -> fnF lvl (fnF lvl acc f1) f2
  | Fnot f1 -> fnF lvl acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fnF lvl (fnF lvl (fnF lvl acc f1) f2) f3
  | Flet (t, (u, f1)) -> fnF (lvl + 1) (fnT lvl acc t) f1
  | Fcase (t, bl) -> List.fold_left (brlvl fnF lvl) (fnT lvl acc t) bl

let all_fnT prT lvl _ t = prT lvl t || raise FoldSkip
let all_fnF prF lvl _ f = prF lvl f || raise FoldSkip
let any_fnT prT lvl _ t = prT lvl t && raise FoldSkip
let any_fnF prF lvl _ f = prF lvl f && raise FoldSkip

let t_all_unsafe prT prF lvl t =
  try t_fold_unsafe (all_fnT prT) (all_fnF prF) lvl true t
  with FoldSkip -> false

let f_all_unsafe prT prF lvl f =
  try f_fold_unsafe (all_fnT prT) (all_fnF prF) lvl true f
  with FoldSkip -> false

let t_any_unsafe prT prF lvl t =
  try t_fold_unsafe (any_fnT prT) (any_fnF prF) lvl false t
  with FoldSkip -> true

let f_any_unsafe prT prF lvl f =
  try f_fold_unsafe (any_fnT prT) (any_fnF prF) lvl false f
  with FoldSkip -> true

(* unsafe constructors with type checking *)

let t_app fs tl ty =
  let s = match fs.ls_value with
    | Some vty -> Ty.matching Mtv.empty vty ty
    | _ -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty t = Ty.matching s ty t.t_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args tl
          with Invalid_argument _ -> raise BadArity);
  t_app fs tl ty

let f_app ps tl =
  let s = match ps.ls_value with
    | None -> Mtv.empty
    | _ -> raise (PredicateSymbolExpected ps)
  in
  let mtch s ty t = Ty.matching s ty t.t_ty in
  ignore (try List.fold_left2 mtch s ps.ls_args tl
          with Invalid_argument _ -> raise BadArity);
  f_app ps tl

let t_case t bl ty =
  let t_check_branch (p, _, tbr) =
    if p.pat_ty != t.t_ty then raise TypeMismatch;
    if tbr.t_ty != ty then raise TypeMismatch
  in
  List.iter t_check_branch bl;
  t_case t bl ty

let f_case t bl =
  let f_check_branch (p, _, fbr) =
    if p.pat_ty != t.t_ty then raise TypeMismatch
  in
  List.iter f_check_branch bl;
  f_case t bl

let t_let v t1 t2 =
  if v.vs_ty != t1.t_ty then raise TypeMismatch;
  t_let v t1 t2

let f_let v t1 f2 =
  if v.vs_ty != t1.t_ty then raise TypeMismatch;
  f_let v t1 f2

(* map over symbols *)

let rec t_s_map fnT fnV fnL t =
  let fn_t = t_s_map fnT fnV fnL in
  let fn_f = f_s_map fnT fnV fnL in
  let ty = fnT t.t_ty in
  t_label_copy t (match t.t_node with
    | Tbvar n -> t_bvar n ty
    | Tvar v -> t_var (fnV v ty)
    | Tconst _ -> t
    | Tapp (f, tl) -> t_app (fnL f) (List.map fn_t tl) ty
    | Tlet (t1, (u, t2)) ->
        let t1 = fn_t t1 in t_let (fnV u t1.t_ty) t1 (fn_t t2)
    | Tcase (t1, bl) ->
        let fn_b = t_branch fnT fnV fnL in
        t_case (fn_t t1) (List.map fn_b bl) ty
    | Teps (u, f) -> t_eps (fnV u ty) (fn_f f))

and t_branch fnT fnV fnL (pat, nv, t) =
  (pat_s_map fnT fnV fnL pat, nv, t_s_map fnT fnV fnL t)

and f_s_map fnT fnV fnL f =
  let fn_t = t_s_map fnT fnV fnL in
  let fn_f = f_s_map fnT fnV fnL in
  f_label_copy f (match f.f_node with
    | Fapp (p, tl) -> f_app (fnL p) (List.map fn_t tl)
    | Fquant (q, (vl, nv, tl, f1)) ->
        let tl = tr_map fn_t fn_f tl in
        let fn_v u = fnV u (fnT u.vs_ty) in
        f_quant q (List.map fn_v vl) nv tl (fn_f f1)
    | Fbinop (op, f1, f2) -> f_binary op (fn_f f1) (fn_f f2)
    | Fnot f1 -> f_not (fn_f f1)
    | Ftrue | Ffalse -> f
    | Fif (f1, f2, f3) -> f_if (fn_f f1) (fn_f f2) (fn_f f3)
    | Flet (t, (u, f1)) ->
        let t1 = fn_t t in f_let (fnV u t1.t_ty) t1 (fn_f f1)
    | Fcase (t, bl) ->
        let fn_b = f_branch fnT fnV fnL in
        f_case (fn_t t) (List.map fn_b bl))

and f_branch fnT fnV fnL (pat, nv, f) =
  (pat_s_map fnT fnV fnL pat, nv, f_s_map fnT fnV fnL f)

let get_fnT fn =
  let ht = Hashtbl.create 17 in
  let fnT ty =
    try Hashtbl.find ht ty.ty_tag with Not_found ->
      let nt = ty_s_map fn ty in
      Hashtbl.add ht ty.ty_tag nt;
      nt
  in
  fnT

let get_fnV () =
  let ht = Hid.create 17 in
  let fnV vs ty =
    if vs.vs_ty == ty then vs else
      try Hid.find ht vs.vs_name with Not_found ->
        let nv = create_vsymbol (id_dup vs.vs_name) ty in
        Hid.add ht vs.vs_name nv;
        nv
  in
  fnV

let t_s_map fnT fnL t = t_s_map (get_fnT fnT) (get_fnV ()) fnL t
let f_s_map fnT fnL f = f_s_map (get_fnT fnT) (get_fnV ()) fnL f

(* fold over symbols *)

let rec t_s_fold fnT fnL acc t =
  let fn_t = t_s_fold fnT fnL in
  let fn_f = f_s_fold fnT fnL in
  let acc = ty_s_fold fnT acc t.t_ty in
  match t.t_node with
    | Tbvar _ | Tvar _ | Tconst _ -> acc
    | Tapp (f, tl) -> List.fold_left fn_t (fnL acc f) tl
    | Tlet (t1, (_,t2)) -> fn_t (fn_t acc t1) t2
    | Tcase (t1, bl) ->
        let fn_b = t_branch fnT fnL in
        List.fold_left fn_b (fn_t acc t1) bl
    | Teps (_,f) -> fn_f acc f

and t_branch fnT fnL acc (pat,_,t) =
  t_s_fold fnT fnL (pat_s_fold fnT fnL acc pat) t

and f_s_fold fnT fnL acc f =
  let fn_t = t_s_fold fnT fnL in
  let fn_f = f_s_fold fnT fnL in
  let fn_v acc u = ty_s_fold fnT acc u.vs_ty in
  match f.f_node with
    | Fapp (p, tl) -> List.fold_left fn_t (fnL acc p) tl
    | Fquant (q, (vl,_,tl,f1)) ->
        let acc = List.fold_left fn_v acc vl in
        fn_f (tr_fold fn_t fn_f acc tl) f1
    | Fbinop (op, f1, f2) -> fn_f (fn_f acc f1) f2
    | Fnot f1 -> fn_f acc f1
    | Ftrue | Ffalse -> acc
    | Fif (f1, f2, f3) -> fn_f (fn_f (fn_f acc f1) f2) f3
    | Flet (t, (_,f1)) -> fn_f (fn_t acc t) f1
    | Fcase (t, bl) ->
        let fn_b = f_branch fnT fnL in
        List.fold_left fn_b (fn_t acc t) bl

and f_branch fnT fnL acc (pat,_,f) =
  f_s_fold fnT fnL (pat_s_fold fnT fnL acc pat) f

let t_s_all prT prL t =
  try t_s_fold (all_fn prT) (all_fn prL) true t with FoldSkip -> false

let f_s_all prT prL f =
  try f_s_fold (all_fn prT) (all_fn prL) true f with FoldSkip -> false

let t_s_any prT prL t =
  try t_s_fold (any_fn prT) (any_fn prL) false t with FoldSkip -> true

let f_s_any prT prL f =
  try f_s_fold (any_fn prT) (any_fn prL) false f with FoldSkip -> true

(* replaces variables with de Bruijn indices in term [t] using map [m] *)

let rec t_abst m lvl t = match t.t_node with
  | Tvar u ->
      (try t_bvar (Mvs.find u m + lvl) t.t_ty with Not_found -> t)
  | _ -> t_map_unsafe (t_abst m) (f_abst m) lvl t

and f_abst m lvl f = f_map_unsafe (t_abst m) (f_abst m) lvl f

let t_abst_single v t = t_abst (Mvs.add v 0 Mvs.empty) 0 t
let f_abst_single v f = f_abst (Mvs.add v 0 Mvs.empty) 0 f

(* replaces de Bruijn indices with variables in term [t] using map [m] *)

module Im = Map.Make(struct type t = int let compare = Pervasives.compare end)

let rec t_inst m lvl t = match t.t_node with
  | Tbvar n when n >= lvl ->
      (try Im.find (n - lvl) m with Not_found -> raise UnboundIndex)
  | _ -> t_map_unsafe (t_inst m) (f_inst m) lvl t

and f_inst m lvl f = f_map_unsafe (t_inst m) (f_inst m) lvl f

let t_inst_single v t = t_inst (Im.add 0 v Im.empty) 0 t
let f_inst_single v f = f_inst (Im.add 0 v Im.empty) 0 f

(* safe smart constructors *)

exception NonLinear of vsymbol

let f_quant q vl tl f = if vl = [] then f else
  let i = ref (-1) in
  let add m v =
    if Mvs.mem v m then raise (NonLinear v);
    incr i; Mvs.add v !i m
  in
  let m = List.fold_left add Mvs.empty vl in
  let tl = tr_map (t_abst m 0) (f_abst m 0) tl in
  f_quant q vl (!i + 1) tl (f_abst m 0 f)

let f_forall = f_quant Fforall
let f_exists = f_quant Fexists

let pat_varmap p =
  let i = ref (-1) in
  let rec mk_map acc p = match p.pat_node with
    | Pvar n ->
        if Mvs.mem n acc then raise (NonLinear n);
        incr i; Mvs.add n !i acc
    | Pas (p, n) ->
        if Mvs.mem n acc then raise (NonLinear n);
        incr i; mk_map (Mvs.add n !i acc) p
    | _ -> pat_fold mk_map acc p
  in
  let m = mk_map Mvs.empty p in
  m, !i + 1

let t_case t bl ty =
  let t_make_branch (p, tbr) =
    let m, nv = pat_varmap p in (p, nv, t_abst m 0 tbr)
  in
  t_case t (List.map t_make_branch bl) ty

let f_case t bl =
  let f_make_branch (p, fbr) =
    let m, nv = pat_varmap p in (p, nv, f_abst m 0 fbr)
  in
  f_case t (List.map f_make_branch bl)

let t_let v t1 t2 = t_let v t1 (t_abst_single v t2)
let f_let v t1 f2 = f_let v t1 (f_abst_single v f2)

let t_eps v f = t_eps v (f_abst_single v f)

(* opening binders *)

let t_open_bound (v, t) =
  let v = fresh_vsymbol v in v, t_inst_single (t_var v) t

let f_open_bound (v, f) =
  let v = fresh_vsymbol v in v, f_inst_single (t_var v) f

let f_open_quant (vl, _, tl, f) =
  let i = ref (-1) in
  let add m v = incr i; Im.add !i (t_var v) m in
  let vl = List.map fresh_vsymbol vl in
  let m = List.fold_left add Im.empty vl in
  let tl = tr_map (t_inst m 0) (f_inst m 0) tl in
  (vl, tl, f_inst m 0 f)

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

let rec pat_rename ns p = match p.pat_node with
  | Pvar n -> pat_var (Mvs.find n ns)
  | Pas (p, n) -> pat_as (pat_rename ns p) (Mvs.find n ns)
  | _ -> pat_map (pat_rename ns) p

let pat_substs pat =
  let m, _ = pat_varmap pat in
  Mvs.fold
    (fun x i (vars, s, ns) ->
       let x' = fresh_vsymbol x in
       Svs.add x' vars, Im.add i (t_var x') s, Mvs.add x x' ns)
    m
    (Svs.empty, Im.empty, Mvs.empty)

let t_open_branch (pat, _, t) =
  let vars, s, ns = pat_substs pat in
  (pat_rename ns pat, vars, t_inst s 0 t)

let f_open_branch (pat, _, f) =
  let vars, s, ns = pat_substs pat in
  (pat_rename ns pat, vars, f_inst s 0 f)

(** Term library *)

(* alpha-equality on patterns *)

let rec pat_equal_alpha p1 p2 =
  p1 == p2 ||
  p1.pat_ty == p2.pat_ty &&
  match p1.pat_node, p2.pat_node with
  | Pwild, Pwild | Pvar _, Pvar _ -> true
  | Papp (f1, l1), Papp (f2, l2) ->
      f1 == f2 && List.for_all2 pat_equal_alpha l1 l2
  | Pas (p1, _), Pas (p2, _) -> pat_equal_alpha p1 p2
  | _ -> false

(* safe opening map *)

let e_equal e1 e2 = match e1, e2 with
  | Term t1, Term t2 -> t1 == t2
  | Fmla f1, Fmla f2 -> f1 == f2
  | _ -> false

let tr_equal = List.for_all2 (List.for_all2 e_equal)

let t_branch fn acc b =
  let pat,_,t = t_open_branch b in let t' = fn t in acc && t' == t, (pat, t')

let f_branch fn acc b =
  let pat,_,f = f_open_branch b in let f' = fn f in acc && f' == f, (pat, f')

let t_map fnT fnF t = t_label_copy t (match t.t_node with
  | Tbvar _ -> raise UnboundIndex
  | Tvar _ | Tconst _ -> t
  | Tapp (f, tl) -> t_app_unsafe f (List.map fnT tl) t.t_ty
  | Tlet (t1, b) -> let u,t2 = t_open_bound b in
      let t1' = fnT t1 in let t2' = fnT t2 in
      if t1' == t1 && t2' == t2 then t else t_let u t1' t2'
  | Tcase (t1, bl) -> let t1' = fnT t1 in
      let same, bl' = map_fold_left (t_branch fnT) true bl in
      if t1' == t1 && same then t else t_case t1' bl' t.t_ty
  | Teps b -> let u,f = f_open_bound b in let f' = fnF f in
      if f' == f then t else t_eps u f')

let f_map fnT fnF f = f_label_copy f (match f.f_node with
  | Fapp (p, tl) -> f_app_unsafe p (List.map fnT tl)
  | Fquant (q, b) -> let vl, tl, f1 = f_open_quant b in
      let f1' = fnF f1 in let tl' = tr_map fnT fnF tl in
      if f1' == f1 && tr_equal tl' tl then f
      else f_quant q vl tl' f1'
  | Fbinop (op, f1, f2) -> f_binary op (fnF f1) (fnF f2)
  | Fnot f1 -> f_not (fnF f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF f1) (fnF f2) (fnF f3)
  | Flet (t, b) -> let u,f1 = f_open_bound b in
      let t' = fnT t in let f1' = fnF f1 in
      if t' == t && f1' == f1 then f else f_let u t' f1'
  | Fcase (t, bl) -> let t' = fnT t in
      let same, bl' = map_fold_left (f_branch fnF) true bl in
      if t' == t && same then f else f_case t' bl')

let protect fn t =
  let res = fn t in
  if res.t_ty != t.t_ty then raise TypeMismatch;
  res

let t_map fnT = t_map (protect fnT)

(* safe opening fold *)

let t_branch fn acc b = let _,_,t = t_open_branch b in fn acc t
let f_branch fn acc b = let _,_,f = f_open_branch b in fn acc f

let t_fold fnT fnF acc t = match t.t_node with
  | Tbvar _ -> raise UnboundIndex
  | Tvar _ | Tconst _ -> acc
  | Tapp (f, tl) -> List.fold_left fnT acc tl
  | Tlet (t1, b) -> let _,t2 = t_open_bound b in fnT (fnT acc t1) t2
  | Tcase (t1, bl) -> List.fold_left (t_branch fnT) (fnT acc t1) bl
  | Teps b -> let _,f = f_open_bound b in fnF acc f

let f_fold fnT fnF acc f = match f.f_node with
  | Fapp (p, tl) -> List.fold_left fnT acc tl
  | Fquant (q, b) -> let vl, tl, f1 = f_open_quant b in
      tr_fold fnT fnF (fnF acc f1) tl
  | Fbinop (op, f1, f2) -> fnF (fnF acc f1) f2
  | Fnot f1 -> fnF acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fnF (fnF (fnF acc f1) f2) f3
  | Flet (t, b) -> let _,f1 = f_open_bound b in fnF (fnT acc t) f1
  | Fcase (t, bl) -> List.fold_left (f_branch fnF) (fnT acc t) bl

let t_all prT prF t =
  try t_fold (all_fn prT) (all_fn prF) true t with FoldSkip -> false

let f_all prT prF f =
  try f_fold (all_fn prT) (all_fn prF) true f with FoldSkip -> false

let t_any prT prF t =
  try t_fold (any_fn prT) (any_fn prF) false t with FoldSkip -> true

let f_any prT prF f =
  try f_fold (any_fn prT) (any_fn prF) false f with FoldSkip -> true

(* map/fold over free variables *)

let rec t_v_map fn lvl t = match t.t_node with
  | Tvar u -> fn u
  | _ -> t_map_unsafe (t_v_map fn) (f_v_map fn) lvl t

and f_v_map fn lvl f = f_map_unsafe (t_v_map fn) (f_v_map fn) lvl f

let rec t_v_fold fn lvl acc t = match t.t_node with
  | Tvar u -> fn acc u
  | _ -> t_fold_unsafe (t_v_fold fn) (f_v_fold fn) lvl acc t

and f_v_fold fn lvl acc f
  = f_fold_unsafe (t_v_fold fn) (f_v_fold fn) lvl acc f

let t_v_all pr t = try t_v_fold (all_fn pr) 0 true t with FoldSkip -> false
let f_v_all pr f = try f_v_fold (all_fn pr) 0 true f with FoldSkip -> false
let t_v_any pr t = try t_v_fold (any_fn pr) 0 false t with FoldSkip -> true
let f_v_any pr f = try f_v_fold (any_fn pr) 0 false f with FoldSkip -> true

let t_v_map fn = t_v_map fn 0
let f_v_map fn = f_v_map fn 0

let t_v_fold fn = t_v_fold fn 0
let f_v_fold fn = f_v_fold fn 0

(* looks for occurrence of a variable from set [s] in a term [t] *)

let t_occurs s t = t_v_any (fun u -> Svs.mem u s) t
let f_occurs s f = f_v_any (fun u -> Svs.mem u s) f

let t_occurs_single v t = t_v_any (fun u -> u == v) t
let f_occurs_single v f = f_v_any (fun u -> u == v) f

(* replaces variables with terms in term [t] using map [m] *)

let find_vs m u = try Mvs.find u m with Not_found -> t_var u

let t_subst m t = t_v_map (find_vs m) t
let f_subst m f = f_v_map (find_vs m) f

let eq_vs v t u = if u == v then t else t_var u

let t_subst_single v t1 t = t_v_map (eq_vs v t1) t
let f_subst_single v t1 f = f_v_map (eq_vs v t1) f

(* set of free variables *)

let t_freevars s t = t_v_fold (fun s u -> Svs.add u s) Svs.empty t
let f_freevars s f = f_v_fold (fun s u -> Svs.add u s) Svs.empty f

(* equality modulo alpha *)

let rec t_equal_alpha t1 t2 =
  t1 == t2 ||
  t1.t_ty == t2.t_ty &&
  match t1.t_node, t2.t_node with
    | Tbvar x1, Tbvar x2 ->
        x1 == x2
    | Tvar v1, Tvar v2 ->
        v1 == v2
    | Tconst c1, Tconst c2 ->
        c1 = c2
    | Tapp (s1, l1), Tapp (s2, l2) ->
        s1 == s2 && List.for_all2 t_equal_alpha l1 l2
    | Tlet (t1, tb1), Tlet (t2, tb2) ->
        let v1, b1 = tb1 in
        let v2, b2 = tb2 in
        t_equal_alpha t1 t2 && t_equal_alpha b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 t_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | Teps fb1, Teps fb2 ->
        let v1, f1 = fb1 in
        let v2, f2 = fb2 in
        f_equal_alpha f1 f2
    | _ -> false

and f_equal_alpha f1 f2 =
  f1 == f2 ||
  match f1.f_node, f2.f_node with
    | Fapp (s1, l1), Fapp (s2, l2) ->
        s1 == s2 && List.for_all2 t_equal_alpha l1 l2
    | Fquant (q1, b1), Fquant (q2, b2) ->
        q1 == q2 && f_equal_quant_alpha b1 b2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) ->
        op1 == op2 && f_equal_alpha f1 f2 && f_equal_alpha g1 g2
    | Fnot f1, Fnot f2 ->
        f_equal_alpha f1 f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        true
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
        f_equal_alpha f1 f2 && f_equal_alpha g1 g2 && f_equal_alpha h1 h2
    | Flet (t1, fb1), Flet (t2, fb2) ->
        let v1, f1 = fb1 in
        let v2, f2 = fb2 in
        t_equal_alpha t1 t2 && f_equal_alpha f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 f_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | _ -> false

and t_equal_branch_alpha br1 br2 =
  let pat1, n1, t1 = br1 in
  let pat2, n2, t2 = br2 in
  n1 == n2 && pat_equal_alpha pat1 pat2 && t_equal_alpha t1 t2

and f_equal_branch_alpha br1 br2 =
  let pat1, n1, f1 = br1 in
  let pat2, n2, f2 = br2 in
  n1 == n2 && pat_equal_alpha pat1 pat2 && f_equal_alpha f1 f2

and f_equal_quant_alpha qf1 qf2 =
  let vl1, n1, _, f1 = qf1 in
  let vl2, n2, _, f2 = qf2 in
  let cmp v1 v2 = v1.vs_ty == v2.vs_ty in
  n1 == n2 && List.for_all2 cmp vl1 vl2 && f_equal_alpha f1 f2

(* looks for free de Bruijn indices *)

let rec t_closed lvl t = match t.t_node with
  | Tbvar x -> x < lvl
  | _ -> t_all_unsafe t_closed f_closed lvl t

and f_closed lvl f = f_all_unsafe t_closed f_closed lvl f

(* matching modulo alpha in the pattern *)

exception NoMatch

let rec t_match s t1 t2 =
  if t1 == t2 then s else
  if t1.t_ty != t2.t_ty then raise NoMatch else
  match t1.t_node, t2.t_node with
    | Tbvar x1, Tbvar x2 when x1 == x2 ->
        s
    | Tconst c1, Tconst c2 when c1 = c2 ->
        s
    | Tvar v1, _ ->
        (try if Mvs.find v1 s == t2 then s else raise NoMatch
        with Not_found -> if t_closed 0 t2
          then Mvs.add v1 t2 s else raise NoMatch)
    | Tapp (s1, l1), Tapp (s2, l2) when s1 == s2 ->
        List.fold_left2 t_match s l1 l2
    | Tlet (t1, tb1), Tlet (t2, tb2) ->
        let v1, b1 = tb1 in
        let v2, b2 = tb2 in
        t_match (t_match s t1 t2) b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        (try List.fold_left2 t_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | Teps fb1, Teps fb2 ->
        let v1, f1 = fb1 in
        let v2, f2 = fb2 in
        f_match s f1 f2
    | _ -> raise NoMatch

and f_match s f1 f2 =
  if f1 == f2 then s else
  match f1.f_node, f2.f_node with
    | Fapp (s1, l1), Fapp (s2, l2) when s1 == s2 ->
        List.fold_left2 t_match s l1 l2
    | Fquant (q1, qf1), Fquant (q2, qf2) when q1 == q2 ->
        f_match_quant s qf1 qf2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) when op1 == op2 ->
        f_match (f_match s f1 f2) g1 g2
    | Fnot f1, Fnot f2 ->
        f_match s f1 f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        s
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
        f_match (f_match (f_match s f1 f2) g1 g2) h1 h2
    | Flet (t1, fb1), Flet (t2, fb2) ->
        let v1, f1 = fb1 in
        let v2, f2 = fb2 in
        f_match (t_match s t1 t2) f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        (try List.fold_left2 f_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | _ -> raise NoMatch

and t_match_branch s br1 br2 =
  let pat1, n1, t1 = br1 in
  let pat2, n2, t2 = br2 in
  if n1 == n2 && pat_equal_alpha pat1 pat2
  then t_match s t1 t2 else raise NoMatch

and f_match_branch s br1 br2 =
  let pat1, n1, f1 = br1 in
  let pat2, n2, f2 = br2 in
  if n1 == n2 && pat_equal_alpha pat1 pat2
  then f_match s f1 f2 else raise NoMatch

and f_match_quant s qf1 qf2 =
  let vl1, n1, _, f1 = qf1 in
  let vl2, n2, _, f2 = qf2 in
  let cmp v1 v2 = v1.vs_ty == v2.vs_ty in
  if n1 == n2 && List.for_all2 cmp vl1 vl2
  then f_match s f1 f2 else raise NoMatch

let t_match t1 t2 s = try Some (t_match s t1 t2) with NoMatch -> None
let f_match f1 f2 s = try Some (f_match s f1 f2) with NoMatch -> None

(* occurrence check *)

let rec t_occurs_term r lvl t = r == t ||
  t_any_unsafe (t_occurs_term r) (f_occurs_term r) lvl t

and f_occurs_term r lvl f =
  f_any_unsafe (t_occurs_term r) (f_occurs_term r) lvl f

let t_occurs_term r t = t_occurs_term r 0 t
let f_occurs_term r f = f_occurs_term r 0 f

let rec t_occurs_fmla r lvl t =
  t_any_unsafe (t_occurs_fmla r) (f_occurs_fmla r) lvl t

and f_occurs_fmla r lvl f = r == f ||
  f_any_unsafe (t_occurs_fmla r) (f_occurs_fmla r) lvl f

let t_occurs_fmla r t = t_occurs_fmla r 0 t
let f_occurs_fmla r f = f_occurs_fmla r 0 f

(* occurrence check modulo alpha *)

let rec t_occurs_term_alpha r lvl t = t_equal_alpha r t ||
  t_any_unsafe (t_occurs_term_alpha r) (f_occurs_term_alpha r) lvl t

and f_occurs_term_alpha r lvl f =
  f_any_unsafe (t_occurs_term_alpha r) (f_occurs_term_alpha r) lvl f

let t_occurs_term_alpha r t = t_occurs_term_alpha r 0 t
let f_occurs_term_alpha r f = f_occurs_term_alpha r 0 f

let rec t_occurs_fmla_alpha r lvl t =
  t_any_unsafe (t_occurs_fmla_alpha r) (f_occurs_fmla_alpha r) lvl t

and f_occurs_fmla_alpha r lvl f = f_equal_alpha r f ||
  f_any_unsafe (t_occurs_fmla_alpha r) (f_occurs_fmla_alpha r) lvl f

let t_occurs_fmla_alpha r t = t_occurs_fmla_alpha r 0 t
let f_occurs_fmla_alpha r f = f_occurs_fmla_alpha r 0 f

(* substitutes term [t2] for term [t1] in term [t] *)

let rec t_subst_term t1 t2 lvl t =
  if t == t1 then t2 else
  t_map_unsafe (t_subst_term t1 t2) (f_subst_term t1 t2) lvl t

and f_subst_term t1 t2 lvl f =
  f_map_unsafe (t_subst_term t1 t2) (f_subst_term t1 t2) lvl f

let t_subst_term t1 t2 t =
  if t1.t_ty == t2.t_ty then t_subst_term t1 t2 0 t
                        else raise TypeMismatch

let f_subst_term t1 t2 f =
  if t1.t_ty == t2.t_ty then f_subst_term t1 t2 0 f
                        else raise TypeMismatch

(* substitutes fmla [f2] for fmla [f1] in term [t] *)

let rec t_subst_fmla f1 f2 lvl t =
  t_map_unsafe (t_subst_fmla f1 f2) (f_subst_fmla f1 f2) lvl t

and f_subst_fmla f1 f2 lvl f =
  if f == f1 then f2 else
  f_map_unsafe (t_subst_fmla f1 f2) (f_subst_fmla f1 f2) lvl f

let t_subst_fmla f1 f2 t = t_subst_fmla f1 f2 0 t
let f_subst_fmla f1 f2 f = f_subst_fmla f1 f2 0 f

(* substitutes term [t2] for term [t1] in term [t] modulo alpha *)

let rec t_subst_term_alpha t1 t2 lvl t =
  if t == t1 then t2 else
  t_map_unsafe (t_subst_term_alpha t1 t2) (f_subst_term_alpha t1 t2) lvl t

and f_subst_term_alpha t1 t2 lvl f =
  f_map_unsafe (t_subst_term_alpha t1 t2) (f_subst_term_alpha t1 t2) lvl f

let t_subst_term_alpha t1 t2 t =
  if t1.t_ty == t2.t_ty then t_subst_term_alpha t1 t2 0 t
                        else raise TypeMismatch

let f_subst_term_alpha t1 t2 f =
  if t1.t_ty == t2.t_ty then f_subst_term_alpha t1 t2 0 f
                        else raise TypeMismatch

(* substitutes fmla [f2] for fmla [f1] in term [t] modulo alpha *)

let rec t_subst_fmla_alpha f1 f2 lvl t =
  t_map_unsafe (t_subst_fmla_alpha f1 f2) (f_subst_fmla_alpha f1 f2) lvl t

and f_subst_fmla_alpha f1 f2 lvl f =
  if f == f1 then f2 else
  f_map_unsafe (t_subst_fmla_alpha f1 f2) (f_subst_fmla_alpha f1 f2) lvl f

let t_subst_fmla_alpha f1 f2 t = t_subst_fmla_alpha f1 f2 0 t
let f_subst_fmla_alpha f1 f2 f = f_subst_fmla_alpha f1 f2 0 f

