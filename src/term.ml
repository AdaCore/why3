(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

type label = string

type vsymbol = Name.t
type vsymbol_set = Name.S.t

module Ty = struct

  type tysymbol = {
    ty_name : Name.t;
    ty_args : vsymbol list;
    ty_def  : ty option;
  }

  and ty = { 
    ty_node : ty_node; 
    ty_tag : int; 
  } 

  and ty_node = 
    | Tyvar of vsymbol
    | Tyapp of tysymbol * ty list

  let create_tysymbol name args def = {
    ty_name = name;
    ty_args = args;
    ty_def = def
  }

  let equal_tysymbol s1 s2 = Name.equal s1.ty_name s2.ty_name
      
  module H = struct

    type t = ty

    let equal ty1 ty2 = match ty1.ty_node, ty2.ty_node with
      | Tyvar n1, Tyvar n2 -> 
	  Name.equal n1 n2
      | Tyapp (s1, l1), Tyapp (s2, l2) -> 
	  equal_tysymbol s1 s2 && List.for_all2 (==) l1 l2
      | _ ->
	  false

    let hash_ty ty = 
      ty.ty_tag

    let hash ty = match ty.ty_node with
      | Tyvar v -> 
	  Name.hash v
      | Tyapp (s, tl) -> 
	  Hashcons.combine_list hash_ty (Name.hash s.ty_name) tl

    let tag n t = { t with ty_tag = n }
    
  end

  module Hty = Hashcons.Make(H)

  let mk_ty n = { ty_node = n; ty_tag = -1 }
  let ty_var n = Hty.hashcons (mk_ty (Tyvar n))
  let ty_app s tl = Hty.hashcons (mk_ty (Tyapp (s, tl)))

end



type tysymbol = Ty.tysymbol
type ty = Ty.ty

type fsymbol = {
  f_name   : Name.t;
  f_scheme : ty list * ty;
}

let create_fsymbol n s = {
  f_name = n;
  f_scheme = s;
}

let eq_fsymbol s1 s2 = Name.equal s1.f_name s2.f_name

type psymbol = {
  p_name   : Name.t;
  p_scheme : ty list;
}

let create_psymbol n s = {
  p_name = n;
  p_scheme = s;
}

let eq_psymbol s1 s2 = Name.equal s1.p_name s2.p_name

type quant = 
  | Fforall
  | Fexists

type binop = 
  | Fand
  | For
  | Fimplies
  | Fiff

type unop =
  | Fnot

type pattern = {
  pat_node : pattern_node;
  pat_vars : Name.S.t;
  pat_tag : int;
}

and pattern_node = 
  | Pwild 
  | Pvar of vsymbol
  | Papp of fsymbol * pattern list
  | Pas of pattern * vsymbol

module Pattern = struct

  type t = pattern

  let equal p1 p2 = match p1.pat_node, p2.pat_node with
    | Pwild, Pwild ->
	true
    | Pvar n1, Pvar n2 ->
	Name.equal n1 n2
    | Papp (s1, l1), Papp (s2, l2) ->
	eq_fsymbol s1 s2 && List.for_all2 (==) l1 l2
    | Pas (p1, n1), Pas (p2, n2) ->
	p1 == p2 && Name.equal n1 n2
    | _ ->
	false

  let hash_pattern p = p.pat_tag

  let hash p = match p.pat_node with
    | Pwild -> 0
    | Pvar n -> Name.hash n
    | Papp (s, pl) -> Hashcons.combine_list hash_pattern (Name.hash s.f_name) pl
    | Pas (p, n) -> Hashcons.combine (hash_pattern p) (Name.hash n)

  let tag n p = { p with pat_tag = n }

end
module Hpattern = Hashcons.Make(Pattern)

let pat_vars acc p = 
  assert (Name.S.is_empty (Name.S.inter acc p.pat_vars));
  Name.S.union acc p.pat_vars

let patn_vars acc = function
  | Pwild -> acc
  | Pvar n -> assert (not (Name.S.mem n acc)); Name.S.add n acc
  | Papp (_, pl) -> List.fold_left pat_vars acc pl 
  | Pas (p, n) -> assert (not (Name.S.mem n acc)); pat_vars (Name.S.add n acc) p

let mk_pattern n = 
  { pat_node = n; pat_vars = patn_vars Name.S.empty n; pat_tag = -1 }
let pat_wild = Hpattern.hashcons (mk_pattern Pwild)
let pat_var n = Hpattern.hashcons (mk_pattern (Pvar n))
let pat_app f pl = Hpattern.hashcons (mk_pattern (Papp (f, pl)))
let pat_as p n = Hpattern.hashcons (mk_pattern (Pas (p, n)))


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
  | Tapp of fsymbol * term list
  | Tcase of term * tbranch list
  | Tlet of term * bind_term
  | Teps of bind_fmla

and fmla_node = 
  | Fapp of psymbol * term list
  | Fquant of quant * bind_fmla
  | Fbinop of binop * fmla * fmla
  | Funop of unop * fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * bind_fmla
  | Fcase of term * fbranch list

and bind_term = vsymbol * ty * term

and tbranch = pattern * term

and bind_fmla = vsymbol * ty * fmla

and fbranch = pattern * fmla

module rec T : Hashcons.HashedType with type t = term = 
struct
  type t = term

  let eq_tbranch (p1, t1) (p2, t2) = 
    p1 == p2 && t1 == t2
    
  let eq_bind_term (v1, ty1, t1) (v2, ty2, t2) = 
    Name.equal v1 v2 && ty1 == ty2 && t1 == t2
    
  let equal_term_node t1 t2 = match t1, t2 with
    | Tbvar x1, Tbvar x2 -> 
	x1 == x2
    | Tvar v1, Tvar v2 -> 
	Name.equal v1 v2
    | Tapp (s1, l1), Tapp (s2, l2) -> 
	Name.equal s1.f_name s2.f_name && List.for_all2 (==) l1 l2
    | Tcase (t1, l1), Tcase (t2, l2) ->
	t1 == t2 && List.for_all2 eq_tbranch l1 l2
    | Tlet (t1, b1), Tlet (t2, b2) ->
	t1 == t2 && eq_bind_term b1 b2
    | Teps f1, Teps f2 ->
	F.eq_bind_fmla f1 f2
    | _ -> 
	false

  let equal t1 t2 =
    equal_term_node t1.t_node t2.t_node && 
    (try List.for_all2 (=) t1.t_label t2.t_label with _ -> false) &&
    t1.t_ty == t2.t_ty

  let hash_bind_term (v, ty, t) = 
    Hashcons.combine2 (Name.hash v) ty.Ty.ty_tag t.t_tag

  let hash_tbranch (p, t) =
    Hashcons.combine p.pat_tag t.t_tag

  let hash_term t = t.t_tag

  let hash_term_node = function
    | Tbvar n -> n
    | Tvar v -> Name.hash v
    | Tapp (f, tl) -> Hashcons.combine_list hash_term (Name.hash f.f_name) tl
    | Tcase (t, bl) -> Hashcons.combine_list hash_tbranch t.t_tag bl
    | Tlet (t, bt) -> Hashcons.combine t.t_tag (hash_bind_term bt)
    | Teps f -> F.hash_bind_fmla f

  let hash t =
    Hashcons.combine (hash_term_node t.t_node) 
      (Hashcons.combine_list Hashtbl.hash t.t_ty.Ty.ty_tag t.t_label)
      
  let tag n t = { t with t_tag = n }
end

and F : sig 
  include Hashcons.HashedType with type t = fmla 
  val eq_bind_fmla : bind_fmla -> bind_fmla -> bool
  val hash_bind_fmla : bind_fmla -> int
end = struct
  type t = fmla

  let eq_fbranch (p1, f1) (p2, f2) = 
    p1 == p2 && f1 == f2
    
  let eq_bind_fmla (v1, ty1, f1) (v2, ty2, f2) =
    Name.equal v1 v2 && ty1 == ty2 && f1 == f2

  let equal_fmla_node f1 f2 = match f1, f2 with
    | Fapp (s1, tl1), Fapp (s2, tl2) ->
	Name.equal s1.p_name s2.p_name && List.for_all2 (==) tl1 tl2
    | Fquant (q1, bf1), Fquant (q2, bf2) ->
	q1 == q2 && eq_bind_fmla bf1 bf2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) ->
	op1 == op2 && f1 == f2 && g1 == g2
    | Funop (op1, f1), Funop (op2, f2) ->
	op1 == op2 && f1 == f2
    | Ftrue, Ftrue 
    | Ffalse, Ffalse ->
	true
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
	f1 == f2 && g1 == g2 && h1 == h2
    | Flet (t1, bf1), Flet (t2, bf2) ->
	t1 == t2 && eq_bind_fmla bf1 bf2
    | Fcase (t1, bl1), Fcase (t2, bl2) ->
	t1 == t2 && List.for_all2 eq_fbranch bl1 bl2
    | _ -> 
	false

  let equal f1 f2 =
    equal_fmla_node f1.f_node f2.f_node && 
    (try List.for_all2 (=) f1.f_label f2.f_label with _ -> false)

  let hash_fmla f = f.f_tag

  let hash_bind_fmla (v, ty, f) = 
    Hashcons.combine2 (Name.hash v) ty.Ty.ty_tag (hash_fmla f)

  let hash_fbranch (p, f) =
    Hashcons.combine p.pat_tag f.f_tag

  let hash_term t = t.t_tag

  let hash_fmla_node = function
    | Fapp (p, tl) -> Hashcons.combine_list hash_term (Name.hash p.p_name) tl
    | Fquant (q, bf) -> Hashcons.combine (Hashtbl.hash q) (hash_bind_fmla bf)
    | Fbinop (op, f1, f2) -> 
	Hashcons.combine2 (Hashtbl.hash op) (hash_fmla f1) (hash_fmla f2)
    | Funop (op, f) -> Hashcons.combine (Hashtbl.hash op) (hash_fmla f)
    | Ftrue -> 0
    | Ffalse -> 1
    | Fif (f1, f2, f3) -> 
	Hashcons.combine2 (hash_fmla f1) (hash_fmla f2) (hash_fmla f3)
    | Flet (t, bf) -> Hashcons.combine t.t_tag (hash_bind_fmla bf)
    | Fcase (t, bl) -> Hashcons.combine_list hash_fbranch t.t_tag bl

  let hash f =
    Hashcons.combine_list Hashtbl.hash (hash_fmla_node f.f_node) f.f_label

  let tag n f = { f with f_tag = n }
end
module Hterm = Hashcons.Make(T)
module Hfmla = Hashcons.Make(F)

(* hash-consing constructors for terms *)

let mk_term n ty = { t_node = n; t_label = []; t_ty = ty; t_tag = -1 }
let t_bvar n ty = Hterm.hashcons (mk_term (Tbvar n) ty)
let t_var v ty = Hterm.hashcons (mk_term (Tvar v) ty)
let t_app f tl ty = Hterm.hashcons (mk_term (Tapp (f, tl)) ty)
let t_label l t = Hterm.hashcons { t with t_label = l }
let t_label_add l t = Hterm.hashcons { t with t_label = l :: t.t_label }

let t_let v t1 t2 = 
  Hterm.hashcons (mk_term (Tlet (t1, (v, t1.t_ty, t2))) t2.t_ty)

let t_case t bl = assert false (*TODO*)
let t_eps u ty f = Hterm.hashcons (mk_term (Teps (u, ty, f)) ty)

(* hash-consing constructors for formulas *)

let mk_fmla n = { f_node = n; f_label = []; f_tag = -1 }
let f_app f tl = Hfmla.hashcons (mk_fmla (Fapp (f, tl)))
let f_true = Hfmla.hashcons (mk_fmla Ftrue)
let f_false = Hfmla.hashcons (mk_fmla Ffalse)
let f_binary op f1 f2 = Hfmla.hashcons (mk_fmla (Fbinop (op, f1, f2)))
let f_and = f_binary Fand
let f_or = f_binary For
let f_implies = f_binary Fimplies
let f_iff = f_binary Fiff
let f_unary op f = Hfmla.hashcons (mk_fmla (Funop (op, f)))
let f_not f = Hfmla.hashcons (mk_fmla (Funop (Fnot, f)))
let f_if f1 f2 f3 = Hfmla.hashcons (mk_fmla (Fif (f1, f2, f3)))
let f_quant q u ty f = Hfmla.hashcons (mk_fmla (Fquant (q, (u, ty, f))))
let f_let v t f = Hfmla.hashcons (mk_fmla (Flet (t, (v, t.t_ty, f))))
let f_case t bl = assert false (*TODO*)

let f_label l f = Hfmla.hashcons { f with f_label = l }
let f_label_add l f = Hfmla.hashcons { f with f_label = l :: f.f_label }

(* substitutions, etc. *)

(* replaces named variables [v] in term [t] by de Bruijn index 0 *)
let rec abs_term lvl v ty t = match t.t_node with
  | Tbvar _ -> 
      t
  | Tvar u when Name.equal u v -> 
      assert (t.t_ty == ty); t_bvar lvl ty
  | Tvar _ ->
      t
  | Tapp (f, tl) -> 
      t_app f (List.map (abs_term lvl v ty) tl) t.t_ty
  | Tcase (t1, bl) -> 
      t_case (abs_term lvl v ty t1) (List.map (abs_tbranch lvl v ty) bl)
  | Tlet (t1, (u, _, t2)) -> 
      t_let u (abs_term lvl v ty t1) (abs_term (lvl + 1) v ty t2)
  | Teps (u, tyu, f) -> 
      t_eps u tyu (abs_fmla (lvl + 1) v ty f)

and abs_tbranch lvl v ty (pat, t) =
  (pat, abs_term (lvl + Name.S.cardinal pat.pat_vars) v ty t)

and abs_fmla lvl v ty f = match f.f_node with
  | Fapp (p, tl) -> 
      f_app p (List.map (abs_term lvl v ty) tl)
  | Fquant (q, (u, tyu, f)) -> 
      f_quant q u tyu (abs_fmla (lvl + 1) v ty f)
  | Fbinop (op, f1, f2) -> 
      f_binary op (abs_fmla lvl v ty f1) (abs_fmla lvl v ty f2)
  | Funop (op, f1) -> 
      f_unary op (abs_fmla lvl v ty f1)
  | Ftrue | Ffalse -> 
      f
  | Fif (f1, f2, f3) -> 
      f_if (abs_fmla lvl v ty f1) (abs_fmla lvl v ty f2) (abs_fmla lvl v ty f3)
  | Flet (t, (u, _, f1)) -> 
      f_let u (abs_term lvl v ty t) (abs_fmla (lvl + 1) v ty f1)
  | Fcase (t, bl) -> 
      f_case (abs_term lvl v ty t) (List.map (abs_fbranch lvl v ty) bl)

and abs_fbranch lvl v ty (pat, f) =
  (pat, abs_fmla (lvl + Name.S.cardinal pat.pat_vars) v ty f)


let t_let v t1 t2 = t_let v t1 (abs_term 0 v t1.t_ty t2)
  
let t_app f tl = assert false (*TODO*)

(* equality *)

let t_equal = (==)
let f_equal = (==)


(********


type node = 
  | BVar of int * int
  | Var of Name.t
  | Tuple of t * t
  | App of t * t
  | Lam of Ty.t * varbind
  | Case of t * case
and t = { tag : int ; node : node }
and varbind = Name.t list * t
and pattern = 
  | PBVar of int
  | PVar of Name.t
  | PTuple of pattern * pattern
  | Wildcard
and case = pattern * varbind
type decl = 
  | Logic of Name.t * Ty.scheme
  | Formula of poly_term

and poly_term = Name.t list * t

module TBase = struct
  type node' = node 
  type node = node'
  type t' = t
  type t = t'

  let rec equal n1 n2 = 
    match n1, n2 with 
    | BVar (i1,j1), BVar (i2,j2) -> i1 = i2 && j1 = j2
    | App (ta1, ta2), App (tb1, tb2) 
    | Tuple (ta1, ta2), Tuple (tb1, tb2) -> 
        equal_t ta1 tb1 && equal_t ta2 tb2
    | Lam (ty1, (n1,t1)), Lam (ty2, (n2,t2)) -> 
         equal_names n1 n2 && equal_t t1 t2 && Ty.hc_equal ty1 ty2
    | Var n1, Var n2 -> Name.equal n1 n2
    | Case (ta,(p1,(n1,t1))), Case (tb,(p2,(n2,t2))) ->
        equal_t ta tb && equal_pattern p1 p2 && 
        equal_names n1 n2 && equal_t t1 t2
    | BVar _, _ | _, BVar _ -> false
    | Var _, _ | _, Var _ -> false
    | App _, _ | _, App _ -> false
    | Tuple _, _ | _, Tuple _ -> false
    | Lam _, _ | _, Lam _ -> false

  and equal_t t1 t2 = t1 == t2
  and equal_names l1 l2 = List.for_all2 Name.equal l1 l2
  and equal_pattern p1 p2 = 
    match p1, p2 with
    | Wildcard, Wildcard -> true
    | PBVar i1, PBVar i2 -> i1 = i2
    | PVar n1, PVar n2 -> Name.equal n1 n2
    | PTuple (ta1, ta2), PTuple (tb1, tb2) -> 
        equal_pattern ta1 tb1 && equal_pattern ta2 tb2
    | Wildcard, _ | _, Wildcard -> false
    | PVar _, _ | _ , PVar _ -> false
    | PBVar _, _| _ , PBVar _ -> false

  let node t = t.node

  open Misc
  let rec hash_pattern p = 
    match p with
    | PBVar i -> combine 7 (hash_int i)
    | PVar n -> combine 8 (Name.hash n)
    | PTuple (p1,p2) -> combine2 9 (hash_pattern p1) (hash_pattern p2)
    | Wildcard -> combine 10 11

  let hash_name_list = 
    List.fold_left (fun acc n -> combine2 4 (Name.hash n) acc)

  let hash n = 
    match n with
    | BVar (i,j) -> combine2 1 (hash_int i) (hash_int j)
    | Var n -> combine 2 (Name.hash n)
    | App (t1,t2) -> combine2 3 t1.tag t2.tag
    | Lam (ty,(n,t)) -> combine2 12 (hash_name_list t.tag n) (Ty.hash ty)
    | Tuple (t1,t2) -> combine2 5 t1.tag t2.tag
    | Case (t,(p,(nl,t2))) -> 
        combine3 6 t.tag (hash_pattern p) (hash_name_list t2.tag nl)
end

module HTerms = Hashcons.Make(TBase)

let equal a b = a.tag = b.tag
let mk_t n t = { tag = t; node = n }
let var n = HTerms.hashcons (Var n) mk_t
let bvar i j = HTerms.hashcons (BVar (i,j)) mk_t
let app t1 t2 = HTerms.hashcons (App (t1,t2)) mk_t
let tuple t1 t2 = HTerms.hashcons (Tuple (t1,t2)) mk_t
let raw_lam t b = HTerms.hashcons (Lam (t,b)) mk_t
let raw_case t p b = HTerms.hashcons (Case (t, (p, b))) mk_t

let build_map nl = 
  let m,_ = 
    List.fold_left (fun (m, i) n -> Name.M.add n i m, i + 1) 
      (Name.M.empty, 0) nl in
  m

let abstract nl t = 
  let m = build_map nl in
  let rec aux i t = 
    match t.node with
    | Var n' ->
        begin try let j = Name.M.find n' m in bvar i j
        with Not_found -> t end
    | BVar _ -> t
    | App (t1,t2) -> app (aux i t1) (aux i t2)
    | Tuple (t1,t2) -> tuple (aux i t1) (aux i t2)
    | Lam (ty, (nl,t)) -> raw_lam ty (nl, aux (i+1) t)
    | Case (ta,(p,(nl,t))) -> raw_case (aux i ta) p (nl, aux (i+1) t) in
  aux 0 t

let abstract_pattern nl p = 
  let m = build_map nl in
  let rec aux p = 
    match p with
    | PVar n ->
        begin try let i = Name.M.find n m in PBVar i
        with Not_found -> p end
    | PBVar _ | Wildcard -> p
    | PTuple (p1,p2) -> PTuple (aux p1, aux p2) in
  aux p


let instantiate tl t = 
  let rec aux i t = 
    match t.node with
    | BVar (i',j) when i = i' -> List.nth tl j
    | BVar _ | Var _ -> t
    | App (t1,t2) -> app (aux i t1) (aux i t2)
    | Tuple (t1,t2) -> tuple (aux i t1) (aux i t2)
    | Lam (ty, (n,t)) -> raw_lam ty (n, aux (i+1) t) 
    | Case (t1, (p,(nl,t2))) -> raw_case (aux i t1) p (nl, aux (i+1) t) in
  aux 0 t

let instantiate_pattern pl p =
  let rec aux p = 
    match p with
    | PBVar i -> List.nth pl i
    | PVar _ | Wildcard -> p
    | PTuple (p1,p2) -> PTuple (aux p1, aux p2) in
  aux p

open Format
let rec print env fmt t = 
  match t.node with
  | BVar (i,j) -> 
      begin try Name.print fmt (List.nth (List.nth env i) j)
      with Invalid_argument "List.nth" -> fprintf fmt "{{%d,%d}}" i j end
  | Var n -> Name.print fmt n
  | App (t1,t2) -> fprintf fmt "%a %a" (print env) t1 (paren env) t2
  | Tuple (t1,t2) -> fprintf fmt "(%a, %a)" (print env) t1 (print env) t2
  | Lam (ty, (n,t)) -> 
      fprintf fmt "(λ%a : %a . %a)" 
        (Misc.print_list Misc.comma Name.print) n 
        (Ty.print []) ty 
        (print (n::env)) t
  | Case (t1, (p,(n,t2))) ->
      fprintf fmt "case %a of %a -> %a" (print env) t1 (print_pattern n) p 
        (print (n::env)) t2
and paren env fmt t = 
  if is_compound t then fprintf fmt "(%a)" (print env) t else print env fmt t
and is_compound t = 
  (* decide if this term has to be printed with parens in some contexts *)
  match t.node with
  | BVar _ | Var _ | Lam _ | Tuple _ -> false
  | App _ | Case _ -> true
and print_pattern l fmt p = 
  match p with
  | PBVar i -> 
      begin try Name.print fmt (List.nth l i)
      with Invalid_argument "List.nth" -> fprintf fmt "{{%d}}" i end
  | PVar v -> Name.print fmt v
  | PTuple (t1,t2) -> 
      fprintf fmt "(%a, %a)" (print_pattern l) t1 (print_pattern l) t2
  | Wildcard -> fprintf fmt "_"

let print = print [] 

let rec alpha_equal a b = 
  if equal a b then true else
    match a.node, b.node with
    | BVar (i1,j1), BVar (i2,j2) -> i1 = i2 && j1 = j2
    | Var n1, Var n2 -> Name.equal n1 n2
    | App (ta1, ta2), App (tb1, tb2)
    | Tuple (ta1, ta2), Tuple (tb1, tb2) ->
        alpha_equal ta1 tb1 && alpha_equal ta2 tb2
    | Lam (ty1, (_,t1)), Lam (ty2, (_,t2)) -> 
        Ty.equal ty1 ty2 && alpha_equal t1 t2
    | Case (ta,(p1,(_,t1))), (Case (tb, (p2,(_,t2)))) ->
        alpha_equal ta tb && TBase.equal_pattern p1 p2 && alpha_equal t1 t2
    | BVar _, _ | _, BVar _ -> false
    | Var _, _ | _, Var _ -> false
    | App _, _ | _, App _ -> false
    | Tuple _, _ | _, Tuple _ -> false
    | Lam _, _ | _, Lam _ -> false


let unsafe_map ~tyfun ~termfun t = 
  let rec aux t = 
    let t = match t.node with
    | BVar _ | Var _ -> t
    | App (t1,t2) -> app (aux t1) (aux t2)
    | Tuple (t1,t2) -> tuple (aux t1) (aux t2)
    | Case (t1, (p,(n,t2))) -> raw_case (aux t1) p (n,aux t2)
    | Lam (ty, (n,t)) -> raw_lam (tyfun ty) (n, aux t) in
    termfun t in
  aux t

let open_ (n,t) = n, instantiate (List.map var n) t

let close n t = 
  let n' = List.map Name.fresh n in
  n', abstract n t

let lam n ty t = raw_lam ty (close [n] t)

let open_case (p,(nl,t)) = 
  let pl = List.map (fun n -> PVar n) nl in
  let tl = List.map var nl in
  instantiate_pattern pl p, nl, instantiate tl t

let close_case p nl t = 
  let nl' = List.map Name.fresh nl in
  abstract_pattern nl p, (nl', abstract nl t)

let case t1 p nl t2 = 
  let p, b = close_case p nl t2 in
  raw_case t1 p b

let wildcard = Wildcard
let pvar x = PVar x
let ptuple p1 p2 = PTuple (p1,p2)

let open_polyterm (nl,t) = 
  let tl = List.map Ty.var nl in
  nl, unsafe_map ~tyfun:(Ty.instantiate tl) ~termfun:(fun x -> x) t

let close_polyterm nl t = 
  let nl' = List.map Name.fresh nl in
  nl', unsafe_map ~tyfun:(Ty.abstract nl) ~termfun:(fun x -> x) t

let open_lam b = 
  let nl, t = open_ b in
  List.hd nl, t



***********)
