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

  exception NoMatching

  let rec matching s ty1 ty2 = match ty1.ty_node, ty2.ty_node with
    | Tyvar n1, _ when Name.M.mem n1 s ->
	if Name.M.find n1 s != ty2 then raise NoMatching;
	s
    | Tyvar n1, _ ->
	Name.M.add n1 ty2 s
    | Tyapp (f1, l1), Tyapp (f2, l2) when Name.equal f1.ty_name f2.ty_name ->
	assert (List.length l1 = List.length l2);
	List.fold_left2 matching s l1 l2
    | _ ->
	raise NoMatching

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
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node = 
  | Pwild 
  | Pvar of vsymbol 
  | Papp of fsymbol * pattern list
  | Pas of pattern * vsymbol

module Pattern = struct

  type t = pattern

  let equal_node p1 p2 = match p1, p2 with
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

  let equal p1 p2 =
    equal_node p1.pat_node p2.pat_node && p1.pat_ty == p2.pat_ty

  let hash_pattern p = p.pat_tag

  let hash_node = function
    | Pwild -> 0
    | Pvar n -> Name.hash n
    | Papp (s, pl) -> Hashcons.combine_list hash_pattern (Name.hash s.f_name) pl
    | Pas (p, n) -> Hashcons.combine (hash_pattern p) (Name.hash n)

  let hash p = Hashcons.combine (hash_node p.pat_node) p.pat_ty.Ty.ty_tag

  let tag n p = { p with pat_tag = n }

end
module Hpattern = Hashcons.Make(Pattern)

let mk_pattern n ty = { pat_node = n; pat_ty = ty; pat_tag = -1 }
let pat_wild ty = Hpattern.hashcons (mk_pattern Pwild ty)
let pat_var n ty = Hpattern.hashcons (mk_pattern (Pvar n) ty)
let pat_app f pl ty = Hpattern.hashcons (mk_pattern (Papp (f, pl)) ty)
let pat_as p n = Hpattern.hashcons (mk_pattern (Pas (p, n)) p.pat_ty)

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

and tbranch = pattern * int * term

and bind_fmla = vsymbol * ty * fmla

and fbranch = pattern * int * fmla

module rec T : Hashcons.HashedType with type t = term = 
struct
  type t = term

  let eq_tbranch (p1, _, t1) (p2, _, t2) = 
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

  let hash_tbranch (p, _, t) =
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

  let eq_fbranch (p1, _, f1) (p2, _, f2) = 
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

  let hash_fbranch (p, _, f) =
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

let t_case t bl ty = Hterm.hashcons (mk_term (Tcase (t, bl)) ty)
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
let f_case t bl = Hfmla.hashcons (mk_fmla (Fcase (t, bl)))

let f_label l f = Hfmla.hashcons { f with f_label = l }
let f_label_add l f = Hfmla.hashcons { f with f_label = l :: f.f_label }

(* abstractions / substitutions *)

let name_map_cardinal m = Name.M.fold (fun _ _ acc -> acc + 1) m 0

(* replaces named variables by de Bruijn indices in term [t] 
   using a map [m] *)
let rec abs_term lvl m t = match t.t_node with
  | Tbvar _ -> 
      t
  | Tvar u -> 
      (try let i = Name.M.find u m in t_bvar (i + lvl) t.t_ty
       with Not_found -> t)
  | Tapp (f, tl) -> 
      t_app f (List.map (abs_term lvl m) tl) t.t_ty
  | Tcase (t1, bl) -> 
      t_case (abs_term lvl m t1) (List.map (abs_tbranch lvl m) bl) t.t_ty
  | Tlet (t1, (u, _, t2)) -> 
      t_let u (abs_term lvl m t1) (abs_term (lvl + 1) m t2)
  | Teps (u, tyu, f) -> 
      t_eps u tyu (abs_fmla (lvl + 1) m f)

and abs_tbranch lvl m (pat, nv, t) =
  (pat, nv, abs_term (lvl + nv) m t)

and abs_fmla lvl m f = match f.f_node with
  | Fapp (p, tl) -> 
      f_app p (List.map (abs_term lvl m) tl)
  | Fquant (q, (u, tyu, f1)) -> 
      f_quant q u tyu (abs_fmla (lvl + 1) m f1)
  | Fbinop (op, f1, f2) -> 
      f_binary op (abs_fmla lvl m f1) (abs_fmla lvl m f2)
  | Funop (op, f1) -> 
      f_unary op (abs_fmla lvl m f1)
  | Ftrue | Ffalse -> 
      f
  | Fif (f1, f2, f3) -> 
      f_if (abs_fmla lvl m f1) (abs_fmla lvl m f2) (abs_fmla lvl m f3)
  | Flet (t, (u, _, f1)) -> 
      f_let u (abs_term lvl m t) (abs_fmla (lvl + 1) m f1)
  | Fcase (t, bl) -> 
      f_case (abs_term lvl m t) (List.map (abs_fbranch lvl m) bl)

and abs_fbranch lvl m (pat, nv, f) =
  (pat, nv, abs_fmla (lvl + nv) m f)

(* applies substitution [s] (mapping de Bruijn variables to terms) to [t2] *)

module Subst = struct
  module Im = Map.Make(
    struct 
      type t = int 
      let compare = Pervasives.compare 
    end)
  type t = term Im.t
  let empty = Im.empty
  let add = Im.add
  let find = Im.find
  let singleton t = Im.add 0 t Im.empty
end


let rec subst_term lvl s t = match t.t_node with
  | Tbvar n when n < lvl -> 
      t
  | Tbvar n ->
      (try t_var (Subst.find (n - lvl) s) t.t_ty
       with Not_found -> assert false)
  | Tvar _ ->
      t
  | Tapp (f, tl) -> 
      t_app f (List.map (subst_term lvl s) tl) t.t_ty
  | Tcase (t1, bl) -> 
      t_case (subst_term lvl s t1) (List.map (subst_tbranch lvl s) bl) t.t_ty
  | Tlet (t1, (u, _, t2)) -> 
      t_let u (subst_term lvl s t1) (subst_term (lvl + 1) s t2)
  | Teps (u, tyu, f) -> 
      t_eps u tyu (subst_fmla (lvl + 1) s f)

and subst_tbranch lvl s (pat, nv, t) =
  (pat, nv, subst_term (lvl + nv) s t)

and subst_fmla lvl s f = match f.f_node with
  | Fapp (p, tl) -> 
      f_app p (List.map (subst_term lvl s) tl)
  | Fquant (q, (u, tyu, f1)) -> 
      f_quant q u tyu (subst_fmla (lvl + 1) s f1)
  | Fbinop (op, f1, f2) -> 
      f_binary op (subst_fmla lvl s f1) (subst_fmla lvl s f2)
  | Funop (op, f1) -> 
      f_unary op (subst_fmla lvl s f1)
  | Ftrue | Ffalse -> 
      f
  | Fif (f1, f2, f3) -> 
      f_if (subst_fmla lvl s f1) (subst_fmla lvl s f2) (subst_fmla lvl s f3)
  | Flet (t, (u, _, f1)) -> 
      f_let u (subst_term lvl s t) (subst_fmla (lvl + 1) s f1)
  | Fcase (t, bl) -> 
      f_case (subst_term lvl s t) (List.map (subst_fbranch lvl s) bl)

and subst_fbranch lvl s (pat, nv, f) =
  (pat, nv, subst_fmla (lvl + nv) s f)

(* smart constructors *)

let name_map_singleton v = Name.M.add v 0 Name.M.empty

(* TODO: checks *)
let t_let v t1 t2 = t_let v t1 (abs_term 0 (name_map_singleton v) t2)

(* TODO: checks *)
let t_eps v ty f = t_eps v ty (abs_fmla 0 (name_map_singleton v) f)  

let t_app f tl ty = 
  let args, res = f.f_scheme in
  let _ = 
    List.fold_left2 
      Ty.matching (Ty.matching Name.M.empty res ty) 
      args (List.map (fun t -> t.t_ty) tl)
  in
  t_app f tl ty

let varmap_for_pattern p =
  let i = ref (-1) in
  let rec make acc p = match p.pat_node with
    | Pwild -> 
	acc
    | Pvar n -> 
	assert (not (Name.M.mem n acc)); 
	incr i; Name.M.add n !i acc
    | Papp (_, pl) -> 
	List.fold_left make acc pl
    | Pas (p, n) -> 
	assert (not (Name.M.mem n acc)); 
	incr i; make (Name.M.add n !i acc) p
  in
  let m = make Name.M.empty p in
  m, !i + 1

(* TODO: checks *)
let t_case t bl = 
  let make_tbranch (p, t) =
    let m, nv = varmap_for_pattern p in (p, nv, abs_term 0 m t)
  in
  t_case t (List.map make_tbranch bl)

(* TODO: checks *)
let f_quant q v ty f = f_quant q v ty (abs_fmla 0 (name_map_singleton v) f) 
let f_forall = f_quant Fforall
let f_exists = f_quant Fexists

(* TODO: checks *)
let f_let v t1 f2 = f_let v t1 (abs_fmla 0 (name_map_singleton v) f2)

let f_app f tl = 
  let args = f.p_scheme in
  let _ = 
    List.fold_left2 
      Ty.matching Name.M.empty
      args (List.map (fun t -> t.t_ty) tl)
  in
  f_app f tl


(* TODO: checks *)
let f_case t bl = 
  let make_fbranch (p, f) =
    let m, nv = varmap_for_pattern p in (p, nv, abs_fmla 0 m f)
  in
  f_case t (List.map make_fbranch bl)

(* opening binders *)

let open_bind_term (v, ty, t) =
  let v = Name.fresh v in
  v, ty, subst_term 0 (Subst.singleton v) t

let rec subst_pat ns p = match p.pat_node with
  | Pwild -> 
      p
  | Pvar n ->
      (try pat_var (Name.M.find n ns) p.pat_ty with Not_found -> assert false)
  | Papp (f, pl) ->
      pat_app f (List.map (subst_pat ns) pl) p.pat_ty
  | Pas (p, n) ->
      pat_as (subst_pat ns p) 
	(try Name.M.find n ns with Not_found -> assert false) 

let substs_for_pat pat =
  let m, _ = varmap_for_pattern pat in
  Name.M.fold 
    (fun x i (vars, s, ns) -> 
       let x' = Name.fresh x in
       Name.S.add x' vars, Subst.add i x' s, Name.M.add x x' ns) 
    m 
    (Name.S.empty, Subst.empty, Name.M.empty)

let open_tbranch (pat, _, t) =
  let vars, s, ns = substs_for_pat pat in
  (subst_pat ns pat, vars, subst_term 0 s t)

let open_bind_fmla (v, ty, f) =
  let v = Name.fresh v in
  v, ty, subst_fmla 0 (Subst.singleton v) f

let open_fbranch (pat, _, f) =
  let vars, s, ns = substs_for_pat pat in
  (subst_pat ns pat, vars, subst_fmla 0 s f)


(* TODO: substitution functions (named variables -> terms)
   performing typing *)

(* equality *)

let t_equal = (==)
let f_equal = (==)

let rec t_alpha_equal t1 t2 = 
  t1 == t2 ||
  t1.t_ty == t2.t_ty &&
  match t1.t_node, t2.t_node with
    | Tbvar x1, Tbvar x2 -> 
	x1 == x2
    | Tvar v1, Tvar v2 -> 
	Name.equal v1 v2
    | Tapp (s1, l1), Tapp (s2, l2) -> 
	Name.equal s1.f_name s2.f_name && List.for_all2 t_alpha_equal l1 l2
    | Tcase (t1, l1), Tcase (t2, l2) ->
	t_alpha_equal t1 t2 && List.for_all2 tbranch_alpha_equal l1 l2
    | Tlet (t1, b1), Tlet (t2, b2) ->
	t_alpha_equal t1 t2 && bind_term_alpha_equal b1 b2
    | Teps f1, Teps f2 ->
	bind_fmla_alpha_equal f1 f2
    | _ -> 
	false
 
and tbranch_alpha_equal (pat1, _, t1) (pat2, _, t2) =
  pat_alpha_equal pat1 pat2 && t_alpha_equal t1 t2

and pat_alpha_equal p1 p2 = match p1.pat_node, p2.pat_node with
  | Pwild, Pwild
  | Pvar _, Pvar _ ->
      true
  | Papp (_, l1), Papp (_, l2) ->
      (try List.for_all2 pat_alpha_equal l1 l2 with _ -> false)
  | Pas (p1, _), Pas (p2, _) ->
      pat_alpha_equal p1 p2
  | _ ->
      false

and bind_term_alpha_equal (_, _, t1) (_, _, t2) =
  t_alpha_equal t1 t2

and bind_fmla_alpha_equal (_, _, f1) (_, _, f2) =
  f_alpha_equal f1 f2

and f_alpha_equal f1 f2 = 
  f1 == f2 ||
  match f1.f_node, f2.f_node with
    | Fapp (s1, tl1), Fapp (s2, tl2) ->
	Name.equal s1.p_name s2.p_name && List.for_all2 t_alpha_equal tl1 tl2
    | Fquant (q1, bf1), Fquant (q2, bf2) ->
	q1 == q2 && bind_fmla_alpha_equal bf1 bf2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) ->
	op1 == op2 && f_alpha_equal f1 f2 && f_alpha_equal g1 g2
    | Funop (op1, f1), Funop (op2, f2) ->
	op1 == op2 && f_alpha_equal f1 f2
    | Ftrue, Ftrue 
    | Ffalse, Ffalse ->
	true
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
	f_alpha_equal f1 f2 && f_alpha_equal g1 g2 && f_alpha_equal h1 h2
    | Flet (t1, bf1), Flet (t2, bf2) ->
	t_alpha_equal t1 t2 && bind_fmla_alpha_equal bf1 bf2
    | Fcase (t1, bl1), Fcase (t2, bl2) ->
	t_alpha_equal t1 t2 && List.for_all2 fbranch_alpha_equal bl1 bl2
    | _ -> 
	false

and fbranch_alpha_equal (pat1, _, f1) (pat2, _, f2) =
  pat_alpha_equal pat1 pat2 && f_alpha_equal f1 f2


