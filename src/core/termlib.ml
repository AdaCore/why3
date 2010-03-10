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
open Term

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

let t_branch fn b = let pat,_,t = t_open_branch b in (pat, fn t)
let f_branch fn b = let pat,_,f = f_open_branch b in (pat, fn f)

let t_map fnT fnF t = t_label_copy t (match t.t_node with
  | Tbvar _ -> raise UnboundIndex
  | Tvar _ | Tconst _ -> t
  | Tapp (f, tl) -> t_app f (List.map fnT tl) t.t_ty
  | Tlet (t1, b) -> let u,t2 = t_open_bound b in t_let u (fnT t1) (fnT t2)
  | Tcase (t1, bl) -> t_case (fnT t1) (List.map (t_branch fnT) bl) t.t_ty
  | Teps b -> let u,f = f_open_bound b in t_eps u (fnF f))

let f_map fnT fnF f = f_label_copy f (match f.f_node with
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
        let v1, b1 = t_open_bound_unsafe tb1 in
        let v2, b2 = t_open_bound_unsafe tb2 in
        t_equal_alpha t1 t2 && t_equal_alpha b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 t_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | Teps fb1, Teps fb2 ->
        let v1, f1 = f_open_bound_unsafe fb1 in
        let v2, f2 = f_open_bound_unsafe fb2 in
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
        let v1, f1 = f_open_bound_unsafe fb1 in
        let v2, f2 = f_open_bound_unsafe fb2 in
        t_equal_alpha t1 t2 && f_equal_alpha f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t_equal_alpha t1 t2 &&
        (try List.for_all2 f_equal_branch_alpha l1 l2
        with Invalid_argument _ -> false)
    | _ -> false

and t_equal_branch_alpha br1 br2 =
  let pat1, n1, t1 = t_open_branch_unsafe br1 in
  let pat2, n2, t2 = t_open_branch_unsafe br2 in
  n1 == n2 && pat_equal_alpha pat1 pat2 && t_equal_alpha t1 t2

and f_equal_branch_alpha br1 br2 =
  let pat1, n1, f1 = f_open_branch_unsafe br1 in
  let pat2, n2, f2 = f_open_branch_unsafe br2 in
  n1 == n2 && pat_equal_alpha pat1 pat2 && f_equal_alpha f1 f2

and f_equal_quant_alpha qf1 qf2 =
  let vl1, n1, _, f1 = f_open_quant_unsafe qf1 in
  let vl2, n2, _, f2 = f_open_quant_unsafe qf2 in
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
        let v1, b1 = t_open_bound_unsafe tb1 in
        let v2, b2 = t_open_bound_unsafe tb2 in
        t_match (t_match s t1 t2) b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        (try List.fold_left2 t_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | Teps fb1, Teps fb2 ->
        let v1, f1 = f_open_bound_unsafe fb1 in
        let v2, f2 = f_open_bound_unsafe fb2 in
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
        let v1, f1 = f_open_bound_unsafe fb1 in
        let v2, f2 = f_open_bound_unsafe fb2 in
        f_match (t_match s t1 t2) f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        (try List.fold_left2 f_match_branch (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | _ -> raise NoMatch

and t_match_branch s br1 br2 =
  let pat1, n1, t1 = t_open_branch_unsafe br1 in
  let pat2, n2, t2 = t_open_branch_unsafe br2 in
  if n1 == n2 && pat_equal_alpha pat1 pat2
  then t_match s t1 t2 else raise NoMatch

and f_match_branch s br1 br2 =
  let pat1, n1, f1 = f_open_branch_unsafe br1 in
  let pat2, n2, f2 = f_open_branch_unsafe br2 in
  if n1 == n2 && pat_equal_alpha pat1 pat2
  then f_match s f1 f2 else raise NoMatch

and f_match_quant s qf1 qf2 =
  let vl1, n1, _, f1 = f_open_quant_unsafe qf1 in
  let vl2, n2, _, f2 = f_open_quant_unsafe qf2 in
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

