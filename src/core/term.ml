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

(** Function symbols *)

type fsymbol = {
  fs_name   : ident;
  fs_scheme : ty list * ty;
  fs_constr : bool;
}

module Fsym = struct
  type t = fsymbol
  let equal = (==)
  let hash fs = fs.fs_name.id_tag
  let compare fs1 fs2 =
    Pervasives.compare fs1.fs_name.id_tag fs2.fs_name.id_tag
end
module Sfs = Set.Make(Fsym)
module Mfs = Map.Make(Fsym)
module Hfs = Hashtbl.Make(Fsym)

let create_fsymbol name scheme constr = {
  fs_name   = id_register name;
  fs_scheme = scheme;
  fs_constr = constr;
}

(** Predicate symbols *)

type psymbol = {
  ps_name   : ident;
  ps_scheme : ty list;
}

module Psym = struct
  type t = psymbol
  let equal = (==)
  let hash ps = ps.ps_name.id_tag
  let compare ps1 ps2 =
    Pervasives.compare ps1.ps_name.id_tag ps2.ps_name.id_tag
end
module Sps = Set.Make(Psym)
module Mps = Map.Make(Psym)
module Hps = Hashtbl.Make(Psym)

let create_psymbol name scheme = {
  ps_name   = id_register name;
  ps_scheme = scheme;
}

(** Patterns *)

type pattern = {
  pat_node : pattern_node;
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of fsymbol * pattern list
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
    | Papp (s, pl) -> Hashcons.combine_list hash_pattern s.fs_name.id_tag pl
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

let pat_map_unsafe fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as (fn p) v

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

exception ConstructorExpected of fsymbol

let pat_app fs pl ty =
  if not fs.fs_constr then raise (ConstructorExpected fs);
  let args, res = fs.fs_scheme in
  ignore (try
    List.fold_left2 Ty.matching
      (Ty.matching Mid.empty res ty)
        args (List.map (fun p -> p.pat_ty) pl)
    with Invalid_argument _ -> raise BadArity);
  pat_app fs pl ty

let pat_as p v =
  if p.pat_ty == v.vs_ty then pat_as p v else raise TypeMismatch

(* safe map over patterns *)

let pat_map fn pat = match pat.pat_node with
  | Pwild | Pvar _ -> pat
  | Papp (s, pl) -> pat_app s (List.map fn pl) pat.pat_ty
  | Pas (p, v) -> pat_as (fn p) v

(* symbol-wise map/fold *)

let rec pat_s_map fnT fnV fnF pat =
  let fn p = pat_s_map fnT fnV fnF p in
  let ty = fnT pat.pat_ty in
  match pat.pat_node with
    | Pwild -> pat_wild ty
    | Pvar v -> pat_var (fnV v ty)
    | Papp (s, pl) -> pat_app (fnF s) (List.map fn pl) ty
    | Pas (p, v) -> pat_as (fn p) (fnV v ty)

let rec pat_s_fold fnT fnF acc pat =
  let fn acc p = pat_s_fold fnT fnF acc p in
  let acc = ty_s_fold fnT acc pat.pat_ty in
  match pat.pat_node with
    | Pwild | Pvar _ -> acc
    | Papp (s, pl) -> List.fold_left fn (fnF acc s) pl
    | Pas (p, _) -> fn acc p

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
  | Tapp of fsymbol * term list
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of fmla_bound

and fmla_node =
  | Fapp of psymbol * term list
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

and trigger_elt =
  | TrTerm of term
  | TrFmla of fmla

and trigger = trigger_elt list

(* trigger traversal *)

let tr_map fnT fnF =
  let fn = function TrTerm t -> TrTerm (fnT t) | TrFmla f -> TrFmla (fnF f) in
  List.map (List.map fn)

let tr_fold fnT fnF =
  let fn acc = function TrTerm t -> fnT acc t | TrFmla f -> fnF acc f in
  List.fold_left (List.fold_left fn)

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
    | Tapp (f, tl) -> Hashcons.combine_list t_hash (f.fs_name.id_tag) tl
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
    | TrTerm t1, TrTerm t2 -> t1 == t2
    | TrFmla f1, TrFmla f2 -> f1 == f2
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

  let tr_hash = function TrTerm t -> t.t_tag | TrFmla f -> f.f_tag

  let f_hash_quant (vl, _, tl, f) =
    let h = Hashcons.combine_list v_hash f.f_tag vl in
    List.fold_left (Hashcons.combine_list tr_hash) h tl

  let f_hash_node = function
    | Fapp (p, tl) -> Hashcons.combine_list t_hash p.ps_name.id_tag tl
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
let t_label_try l t = if l == []  then t else t_label l t

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
let f_label_try l f = if l == []  then f else f_label l f

(* unsafe map with level *)

let brlvl fn lvl (pat, nv, t) = (pat, nv, fn (lvl + nv) t)

let t_map_unsafe fnT fnF lvl t = t_label_try t.t_label (match t.t_node with
  | Tbvar _ | Tvar _ | Tconst _ -> t
  | Tapp (f, tl) -> t_app f (List.map (fnT lvl) tl) t.t_ty
  | Tlet (t1, (u, t2)) -> t_let u (fnT lvl t1) (fnT (lvl + 1) t2)
  | Tcase (t1, bl) -> t_case (fnT lvl t1) (List.map (brlvl fnT lvl) bl) t.t_ty
  | Teps (u, f) -> t_eps u (fnF (lvl + 1) f))

let f_map_unsafe fnT fnF lvl f = f_label_try f.f_label (match f.f_node with
  | Fapp (p, tl) -> f_app p (List.map (fnT lvl) tl)
  | Fquant (q, (vl, nv, tl, f1)) -> let lvl = lvl + nv in
      f_quant q vl nv (tr_map (fnT lvl) (fnF lvl) tl) (fnF lvl f1)
  | Fbinop (op, f1, f2) -> f_binary op (fnF lvl f1) (fnF lvl f2)
  | Fnot f1 -> f_not (fnF lvl f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF lvl f1) (fnF lvl f2) (fnF lvl f3)
  | Flet (t, (u, f1)) -> f_let u (fnT lvl t) (fnF (lvl + 1) f1)
  | Fcase (t, bl) -> f_case (fnT lvl t) (List.map (brlvl fnF lvl) bl))

(* unsafe fold with level *)

let brlvl fn lvl acc (_, nv, t) = fn (lvl + nv) acc t

let t_fold_unsafe fnT fnF lvl acc t = match t.t_node with
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
      (try Im.find (n - lvl) m with Not_found -> assert false)
  | _ -> t_map_unsafe (t_inst m) (f_inst m) lvl t

and f_inst m lvl f = f_map_unsafe (t_inst m) (f_inst m) lvl f

let t_inst_single v t = t_inst (Im.add 0 v Im.empty) 0 t
let f_inst_single v f = f_inst (Im.add 0 v Im.empty) 0 f

(* looks for free de Bruijn indices *)

let rec t_closed lvl t = match t.t_node with
  | Tbvar x -> x < lvl
  | _ -> t_all_unsafe t_closed f_closed lvl t

and f_closed lvl f = f_all_unsafe t_closed f_closed lvl f

(* map/fold over free variables *)

let rec t_v_map fn lvl t = match t.t_node with
  | Tvar u ->
      let v = fn u in
      if v.t_ty != u.vs_ty then raise TypeMismatch;
      v
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
        (* assert (List.length l1 == List.length l2); *)
        s1 == s2 && List.for_all2 t_equal_alpha l1 l2
    | Tlet (t1, (v1, b1)), Tlet (t2, (v2, b2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_equal_alpha t1 t2 && t_equal_alpha b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 t_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | Teps (v1, f1), Teps (v2, f2) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        f_equal_alpha f1 f2
    | _ -> false

and f_equal_alpha f1 f2 =
  f1 == f2 ||
  match f1.f_node, f2.f_node with
    | Fapp (s1, l1), Fapp (s2, l2) ->
        (* assert (List.length l1 == List.length l2); *)
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
    | Flet (t1, (v1, f1)), Flet (t2, (v2, f2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_equal_alpha t1 t2 && f_equal_alpha f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 f_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | _ -> false

and t_equal_branch_alpha (pat1, _, t1) (pat2, _, t2) =
  pat_equal_alpha pat1 pat2 && t_equal_alpha t1 t2

and f_equal_branch_alpha (pat1, _, f1) (pat2, _, f2) =
  pat_equal_alpha pat1 pat2 && f_equal_alpha f1 f2

and f_equal_quant_alpha (vl1, nv1, tl1, f1) (vl2, nv2, tl2, f2) =
  nv1 == nv2 && List.for_all2 (fun v1 v2 -> v1.vs_ty == v2.vs_ty) vl1 vl2 &&
    f_equal_alpha f1 f2

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
        (* assert (List.length l1 == List.length l2); *)
        List.fold_left2 t_match s l1 l2
    | Tlet (t1, (v1, b1)), Tlet (t2, (v2, b2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_match (t_match s t1 t2) b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        (try List.fold_left2 t_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | Teps (v1, f1), Teps (v2, f2) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        f_match s f1 f2
    | _ -> raise NoMatch

and f_match s f1 f2 =
  if f1 == f2 then s else
  match f1.f_node, f2.f_node with
    | Fapp (s1, l1), Fapp (s2, l2) when s1 == s2 ->
        (* assert (List.length l1 == List.length l2); *)
        List.fold_left2 t_match s l1 l2
    | Fquant (q1, (vl1, nv1, _, f1)), Fquant (q2, (vl2, nv2, _, f2))
        when q1 == q2 && nv1 == nv2 &&
          List.for_all2 (fun v1 v2 -> v1.vs_ty == v2.vs_ty) vl1 vl2 ->
        f_match s f1 f2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) when op1 == op2 ->
        f_match (f_match s f1 f2) g1 g2
    | Fnot f1, Fnot f2 ->
        f_match s f1 f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        s
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
        f_match (f_match (f_match s f1 f2) g1 g2) h1 h2
    | Flet (t1, (v1, f1)), Flet (t2, (v2, f2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        f_match (t_match s t1 t2) f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        (try List.fold_left2 f_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | _ -> raise NoMatch

and t_match_branch s (pat1, _, t1) (pat2, _, t2) =
  if pat_equal_alpha pat1 pat2 then t_match s t1 t2 else raise NoMatch

and f_match_branch s (pat1, _, f1) (pat2, _, f2) =
  if pat_equal_alpha pat1 pat2 then f_match s f1 f2 else raise NoMatch

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

(* unsafe constructors with type checking *)

let t_let v t1 t2 =
  if v.vs_ty == t1.t_ty then t_let v t1 t2 else raise TypeMismatch

let f_let v t1 f2 =
  if v.vs_ty == t1.t_ty then f_let v t1 f2 else raise TypeMismatch

let t_app f tl ty =
  let args, res = f.fs_scheme in
  let _ =
    try List.fold_left2 Ty.matching
        (Ty.matching Mid.empty res ty)
        args (List.map (fun t -> t.t_ty) tl)
    with Invalid_argument _ -> raise BadArity
  in
  t_app f tl ty

let f_app p tl =
  let _ =
    try List.fold_left2 Ty.matching Mid.empty
        p.ps_scheme (List.map (fun t -> t.t_ty) tl)
    with Invalid_argument _ -> raise BadArity
  in
  f_app p tl

let t_case t bl ty =
  let t_check_branch (p, _, tbr) =
    if tbr.t_ty != ty then raise TypeMismatch;
    if p.pat_ty != t.t_ty then raise TypeMismatch
  in
  List.iter t_check_branch bl;
  t_case t bl ty

let f_case t bl =
  let f_check_branch (p, _, fbr) =
    if p.pat_ty != t.t_ty then raise TypeMismatch
  in
  List.iter f_check_branch bl;
  f_case t bl

(* symbol-wise map *)

let rec t_s_map fnT fnV fnF fnP t =
  let fn_t = t_s_map fnT fnV fnF fnP in
  let fn_f = f_s_map fnT fnV fnF fnP in
  let ty = fnT t.t_ty in
  t_label_try t.t_label (match t.t_node with
    | Tbvar n -> t_bvar n ty
    | Tvar v -> t_var (fnV v ty)
    | Tconst _ -> t
    | Tapp (f, tl) -> t_app (fnF f) (List.map fn_t tl) ty
    | Tlet (t1, (u, t2)) ->
        let t1 = fn_t t1 in t_let (fnV u t1.t_ty) t1 (fn_t t2)
    | Tcase (t1, bl) ->
        let fn_b = t_branch fnT fnV fnF fnP in
        t_case (fn_t t1) (List.map fn_b bl) ty
    | Teps (u, f) -> t_eps (fnV u ty) (fn_f f))

and t_branch fnT fnV fnF fnP (pat, nv, t) =
  (pat_s_map fnT fnV fnF pat, nv, t_s_map fnT fnV fnF fnP t)

and f_s_map fnT fnV fnF fnP f =
  let fn_t = t_s_map fnT fnV fnF fnP in
  let fn_f = f_s_map fnT fnV fnF fnP in
  f_label_try f.f_label (match f.f_node with
    | Fapp (p, tl) -> f_app (fnP p) (List.map fn_t tl)
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
        let fn_b = f_branch fnT fnV fnF fnP in
        f_case (fn_t t) (List.map fn_b bl))

and f_branch fnT fnV fnF fnP (pat, nv, f) =
  (pat_s_map fnT fnV fnF pat, nv, f_s_map fnT fnV fnF fnP f)

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

let get_fnT fn =
  let ht = Hashtbl.create 17 in
  let fnT ty =
    try Hashtbl.find ht ty.ty_tag with Not_found ->
      let nt = ty_s_map fn ty in
      Hashtbl.add ht ty.ty_tag nt;
      nt
  in
  fnT

let t_s_map fnT fnF fnP t = t_s_map (get_fnT fnT) (get_fnV ()) fnF fnP t
let f_s_map fnT fnF fnP f = f_s_map (get_fnT fnT) (get_fnV ()) fnF fnP f

(* symbol-wise fold *)

let rec t_s_fold fnT fnF fnP acc t =
  let fn_t = t_s_fold fnT fnF fnP in
  let fn_f = f_s_fold fnT fnF fnP in
  let acc = ty_s_fold fnT acc t.t_ty in
  match t.t_node with
    | Tbvar _ | Tvar _ | Tconst _ -> acc
    | Tapp (f, tl) -> List.fold_left fn_t (fnF acc f) tl
    | Tlet (t1, (_,t2)) -> fn_t (fn_t acc t1) t2
    | Tcase (t1, bl) ->
        let fn_b = t_branch fnT fnF fnP in
        List.fold_left fn_b (fn_t acc t1) bl
    | Teps (_,f) -> fn_f acc f

and t_branch fnT fnF fnP acc (pat,_,t) =
  t_s_fold fnT fnF fnP (pat_s_fold fnT fnF acc pat) t

and f_s_fold fnT fnF fnP acc f =
  let fn_t = t_s_fold fnT fnF fnP in
  let fn_f = f_s_fold fnT fnF fnP in
  let fn_v acc u = ty_s_fold fnT acc u.vs_ty in
  match f.f_node with
    | Fapp (p, tl) -> List.fold_left fn_t (fnP acc p) tl
    | Fquant (q, (vl,_,tl,f1)) ->
        let acc = List.fold_left fn_v acc vl in
        fn_f (tr_fold fn_t fn_f acc tl) f1
    | Fbinop (op, f1, f2) -> fn_f (fn_f acc f1) f2
    | Fnot f1 -> fn_f acc f1
    | Ftrue | Ffalse -> acc
    | Fif (f1, f2, f3) -> fn_f (fn_f (fn_f acc f1) f2) f3
    | Flet (t, (_,f1)) -> fn_f (fn_t acc t) f1
    | Fcase (t, bl) ->
        let fn_b = f_branch fnT fnF fnP in
        List.fold_left fn_b (fn_t acc t) bl

and f_branch fnT fnF fnP acc (pat,_,f) =
  f_s_fold fnT fnF fnP (pat_s_fold fnT fnF acc pat) f

let t_s_all prT prF prP t =
  try t_s_fold (all_fn prT) (all_fn prF) (all_fn prP) true t
  with FoldSkip -> false

let f_s_all prT prF prP f =
  try f_s_fold (all_fn prT) (all_fn prF) (all_fn prP) true f
  with FoldSkip -> false

let t_s_any prT prF prP t =
  try t_s_fold (any_fn prT) (any_fn prF) (any_fn prP) false t
  with FoldSkip -> true

let f_s_any prT prF prP f =
  try f_s_fold (any_fn prT) (any_fn prF) (any_fn prP) false f
  with FoldSkip -> true

(* safe smart constructors *)

let t_let v t1 t2 = t_let v t1 (t_abst_single v t2)
let f_let v t1 f2 = f_let v t1 (f_abst_single v f2)

let t_eps v f = t_eps v (f_abst_single v f)

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

let rec pat_rename ns p = match p.pat_node with
  | Pvar n -> pat_var (Mvs.find n ns)
  | Pas (p, n) -> pat_as (pat_rename ns p) (Mvs.find n ns)
  | _ -> pat_map_unsafe (pat_rename ns) p

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

(* safe opening map *)

let t_branch fn b = let pat,_,t = t_open_branch b in (pat, fn t)
let f_branch fn b = let pat,_,f = f_open_branch b in (pat, fn f)

let t_map fnT fnF t = t_label_try t.t_label (match t.t_node with
  | Tbvar _ -> assert false
  | Tvar _ | Tconst _ -> t
  | Tapp (f, tl) -> t_app f (List.map fnT tl) t.t_ty
  | Tlet (t1, b) -> let u,t2 = t_open_bound b in t_let u (fnT t1) (fnT t2)
  | Tcase (t1, bl) -> t_case (fnT t1) (List.map (t_branch fnT) bl) t.t_ty
  | Teps b -> let u,f = f_open_bound b in t_eps u (fnF f))

let f_map fnT fnF f = f_label_try f.f_label (match f.f_node with
  | Fapp (p, tl) -> f_app p (List.map fnT tl)
  | Fquant (q, b) -> let vl, tl, f1 = f_open_quant b in
      f_quant q vl (tr_map fnT fnF tl) (fnF f1)
  | Fbinop (op, f1, f2) -> f_binary op (fnF f1) (fnF f2)
  | Fnot f1 -> f_not (fnF f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF f1) (fnF f2) (fnF f3)
  | Flet (t, b) -> let u,f1 = f_open_bound b in f_let u (fnT t) (fnF f1)
  | Fcase (t, bl) -> f_case (fnT t) (List.map (f_branch fnF) bl))

(* safe opening fold *)

let t_branch fn acc b = let _,_,t = t_open_branch b in fn acc t
let f_branch fn acc b = let _,_,f = f_open_branch b in fn acc f

let t_fold fnT fnF acc t = match t.t_node with
  | Tbvar _ -> assert false
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

(* built-in symbols *)

let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix =") [v; v]

let ps_neq =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "infix <>") [v; v]

(* FIXME: is it right to do so? *)
let f_app p tl =
  if p == ps_neq then f_not (f_app ps_equ tl) else f_app p tl

let f_equ t1 t2 = f_app ps_equ [t1; t2]
let f_neq t1 t2 = f_app ps_neq [t1; t2]

