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

(** Types *)

module Ty = struct

  type tvsymbol = Name.t

  (* type symbols and types *)

  type tysymbol = {
    ts_name : Name.t;
    ts_args : tvsymbol list;
    ts_def  : ty option;
    ts_tag  : int;
  }

  and ty = {
    ty_node : ty_node;
    ty_tag : int;
  }

  and ty_node =
    | Tyvar of tvsymbol
    | Tyapp of tysymbol * ty list

  module Tsym = struct
    type t = tysymbol
    let equal ts1 ts2 = Name.equal ts1.ts_name ts2.ts_name
    let hash ts = Name.hash ts.ts_name
    let tag n ts = { ts with ts_tag = n }
  end
  module Hts = Hashcons.Make(Tsym)

  let mk_ts name args def = {
    ts_name = name;
    ts_args = args;
    ts_def  = def;
    ts_tag  = -1
  }

  let create_tysymbol name args def = Hts.hashcons (mk_ts name args def)

  module Ty = struct

    type t = ty

    let equal ty1 ty2 = match ty1.ty_node, ty2.ty_node with
      | Tyvar n1, Tyvar n2 -> Name.equal n1 n2
      | Tyapp (s1, l1), Tyapp (s2, l2) -> s1 == s2 && List.for_all2 (==) l1 l2
      | _ -> false

    let hash_ty ty = ty.ty_tag

    let hash ty = match ty.ty_node with
      | Tyvar v -> Name.hash v
      | Tyapp (s, tl) -> Hashcons.combine_list hash_ty (s.ts_tag) tl

    let tag n ty = { ty with ty_tag = n }

  end
  module Hty = Hashcons.Make(Ty)

  let mk_ty n = { ty_node = n; ty_tag = -1 }
  let ty_var n = Hty.hashcons (mk_ty (Tyvar n))
  let ty_app s tl = Hty.hashcons (mk_ty (Tyapp (s, tl)))

  exception BadTypeArity

  let ty_app s tl =
    if List.length tl == List.length s.ts_args
      then ty_app s tl else raise BadTypeArity

  exception TypeMismatch

  let rec matching s ty1 ty2 =
    if ty1 == ty2 then s
    else match ty1.ty_node, ty2.ty_node with
      | Tyvar n1, _ ->
          (try if Name.M.find n1 s == ty2 then s else raise TypeMismatch
          with Not_found -> Name.M.add n1 ty2 s)
      | Tyapp (f1, l1), Tyapp (f2, l2) when f1 == f2 ->
          List.fold_left2 matching s l1 l2
      | _ ->
          raise TypeMismatch

  let ty_match ty1 ty2 s =
    try Some (matching s ty1 ty2) with TypeMismatch -> None

end

type tvsymbol = Ty.tvsymbol
type tysymbol = Ty.tysymbol
type ty = Ty.ty

(** Variable symbols *)

type vsymbol = {
  vs_name : Name.t;
  vs_ty   : ty;
  vs_tag  : int;
}

module Vsym = struct
  type t = vsymbol
  let equal vs1 vs2 = Name.equal vs1.vs_name vs2.vs_name
  let hash vs = Name.hash vs.vs_name
  let tag n vs = { vs with vs_tag = n }
  let compare vs1 vs2 = Pervasives.compare vs1.vs_tag vs2.vs_tag
end

module Hvs = Hashcons.Make(Vsym)
module Mvs = Map.Make(Vsym)
module Svs = Set.Make(Vsym)

let mk_vs name ty = { vs_name = name; vs_ty = ty; vs_tag = -1 }
let create_vsymbol name ty = Hvs.hashcons (mk_vs name ty)

(* TODO: needs refactoring *)
let fresh_vsymbol v = create_vsymbol (Name.fresh v.vs_name) v.vs_ty

(** Function symbols *)

type fsymbol = {
  fs_name   : Name.t;
  fs_scheme : ty list * ty;
  fs_constr : bool;
  fs_tag    : int;
}

module Fsym = struct
  type t = fsymbol
  let equal fs1 fs2 = Name.equal fs1.fs_name fs2.fs_name
  let hash fs = Name.hash fs.fs_name
  let tag n fs = { fs with fs_tag = n }
end
module Hfs = Hashcons.Make(Fsym)

let mk_fs name scheme constr = {
  fs_name = name;
  fs_scheme = scheme;
  fs_constr = constr;
  fs_tag = -1
}

let create_fsymbol name scheme constr = Hfs.hashcons (mk_fs name scheme constr)

(** Predicate symbols *)

type psymbol = {
  ps_name   : Name.t;
  ps_scheme : ty list;
  ps_tag    : int;
}

module Psym = struct
  type t = psymbol
  let equal ps1 ps2 = Name.equal ps1.ps_name ps2.ps_name
  let hash ps = Name.hash ps.ps_name
  let tag n ps = { ps with ps_tag = n }
end
module Hps = Hashcons.Make(Psym)

let mk_ps name scheme = { ps_name = name; ps_scheme = scheme; ps_tag = -1 }
let create_psymbol name scheme = Hps.hashcons (mk_ps name scheme)

(** Hpats *)

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
    | Pvar v -> v.vs_tag
    | Papp (s, pl) -> Hashcons.combine_list hash_pattern s.fs_tag pl
    | Pas (p, v) -> Hashcons.combine (hash_pattern p) v.vs_tag

  let hash p = Hashcons.combine (hash_node p.pat_node) p.pat_ty.Ty.ty_tag

  let tag n p = { p with pat_tag = n }

end
module Hp = Hashcons.Make(Hpat)

(* h-consing constructors for patterns *)

let mk_pattern n ty = { pat_node = n; pat_ty = ty; pat_tag = -1 }
let pat_wild ty = Hp.hashcons (mk_pattern Pwild ty)
let pat_var v = Hp.hashcons (mk_pattern (Pvar v) v.vs_ty)
let pat_app f pl ty = Hp.hashcons (mk_pattern (Papp (f, pl)) ty)
let pat_as p v = Hp.hashcons (mk_pattern (Pas (p, v)) p.pat_ty)

(* smart constructors for patterns *)

exception BadArity

exception ConstructorExpected

let pat_app f pl ty =
  if not f.fs_constr then raise ConstructorExpected else
  let args, res = f.fs_scheme in
  let _ =
    try List.fold_left2 Ty.matching
        (Ty.matching Name.M.empty res ty)
        args (List.map (fun p -> p.pat_ty) pl)
    with Invalid_argument _ -> raise BadArity
  in
  pat_app f pl ty

let pat_as p v =
  if p.pat_ty == v.vs_ty then pat_as p v else raise Ty.TypeMismatch

(* alpha-equality on patterns *)

let rec pat_alpha_equal p1 p2 =
  p1 == p2 ||
  p1.pat_ty == p2.pat_ty &&
  match p1.pat_node, p2.pat_node with
  | Pwild, Pwild | Pvar _, Pvar _ -> true
  | Papp (f1, l1), Papp (f2, l2) ->
      f1 == f2 && List.for_all2 pat_alpha_equal l1 l2
  | Pas (p1, _), Pas (p2, _) -> pat_alpha_equal p1 p2
  | _ -> false

(** Terms and formulas *)

type quant =
  | Fforall
  | Fexists

type binop =
  | Fand
  | For
  | Fimplies
  | Fiff

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
  | Tlet of term * bind_term
  | Tcase of term * tbranch list
  | Teps of bind_fmla

and fmla_node =
  | Fapp of psymbol * term list
  | Fquant of quant * bind_fmla
  | Fbinop of binop * fmla * fmla
  | Fnot of fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * bind_fmla
  | Fcase of term * fbranch list

and bind_term = vsymbol * term

and bind_fmla = vsymbol * fmla

and tbranch = pattern * int * term

and fbranch = pattern * int * fmla

module T = struct

  type t = term

  let eq_tbranch (p1, _, t1) (p2, _, t2) = p1 == p2 && t1 == t2

  let eq_bind_term (v1, t1) (v2, t2) = v1 == v2 && t1 == t2

  let eq_bind_fmla (v1, f1) (v2, f2) = v1 == v2 && f1 == f2

  let equal_term_node t1 t2 = match t1, t2 with
    | Tbvar x1, Tbvar x2 -> x1 == x2
    | Tvar v1, Tvar v2 -> v1 == v2
    | Tapp (s1, l1), Tapp (s2, l2) -> s1 == s2 && List.for_all2 (==) l1 l2
    | Tlet (t1, b1), Tlet (t2, b2) -> t1 == t2 && eq_bind_term b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t1 == t2 &&
        (try List.for_all2 eq_tbranch l1 l2
        with Invalid_argument _ -> false)
    | Teps f1, Teps f2 -> eq_bind_fmla f1 f2
    | _ -> false

  let equal t1 t2 =
    equal_term_node t1.t_node t2.t_node &&
    t1.t_ty == t2.t_ty &&
    try List.for_all2 (=) t1.t_label t2.t_label
    with Invalid_argument _ -> false

  let hash_tbranch (p, _, t) = Hashcons.combine p.pat_tag t.t_tag

  let hash_bind_term (v, t) = Hashcons.combine v.vs_tag t.t_tag

  let hash_bind_fmla (v, f) = Hashcons.combine v.vs_tag f.f_tag

  let hash_term t = t.t_tag

  let hash_term_node = function
    | Tbvar n -> n
    | Tvar v -> v.vs_tag
    | Tapp (f, tl) -> Hashcons.combine_list hash_term (f.fs_tag) tl
    | Tlet (t, bt) -> Hashcons.combine t.t_tag (hash_bind_term bt)
    | Tcase (t, bl) -> Hashcons.combine_list hash_tbranch t.t_tag bl
    | Teps f -> hash_bind_fmla f

  let hash t =
    Hashcons.combine (hash_term_node t.t_node)
      (Hashcons.combine_list Hashtbl.hash t.t_ty.Ty.ty_tag t.t_label)

  let tag n t = { t with t_tag = n }

  let compare t1 t2 = Pervasives.compare t1.t_tag t2.t_tag

end
module Hterm = Hashcons.Make(T)
module Mterm = Map.Make(T)
module Sterm = Set.Make(T)

module F = struct

  type t = fmla

  let eq_fbranch (p1, _, f1) (p2, _, f2) = p1 == p2 && f1 == f2

  let eq_bind_fmla (v1, f1) (v2, f2) = v1 == v2 && f1 == f2

  let equal_fmla_node f1 f2 = match f1, f2 with
    | Fapp (s1, l1), Fapp (s2, l2) ->
        s1 == s2 && List.for_all2 (==) l1 l2
    | Fquant (q1, b1), Fquant (q2, b2) ->
        q1 == q2 && eq_bind_fmla b1 b2
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
        t1 == t2 && eq_bind_fmla b1 b2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t1 == t2 &&
        (try List.for_all2 eq_fbranch l1 l2
        with Invalid_argument _ -> false)
    | _ ->
        false

  let equal f1 f2 =
    equal_fmla_node f1.f_node f2.f_node &&
    try List.for_all2 (=) f1.f_label f2.f_label
    with Invalid_argument _ -> false

  let hash_fbranch (p, _, f) = Hashcons.combine p.pat_tag f.f_tag

  let hash_bind_fmla (v, f) = Hashcons.combine v.vs_tag f.f_tag

  let hash_term t = t.t_tag

  let hash_fmla f = f.f_tag

  let hash_fmla_node = function
    | Fapp (p, tl) -> Hashcons.combine_list hash_term p.ps_tag tl
    | Fquant (q, bf) -> Hashcons.combine (Hashtbl.hash q) (hash_bind_fmla bf)
    | Fbinop (op, f1, f2) ->
        Hashcons.combine2 (Hashtbl.hash op) f1.f_tag f2.f_tag
    | Fnot f -> Hashcons.combine 1 f.f_tag
    | Ftrue -> 0
    | Ffalse -> 1
    | Fif (f1, f2, f3) -> Hashcons.combine2 f1.f_tag f2.f_tag f3.f_tag
    | Flet (t, bf) -> Hashcons.combine t.t_tag (hash_bind_fmla bf)
    | Fcase (t, bl) -> Hashcons.combine_list hash_fbranch t.t_tag bl

  let hash f =
    Hashcons.combine_list Hashtbl.hash (hash_fmla_node f.f_node) f.f_label

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
let t_app f tl ty = Hterm.hashcons (mk_term (Tapp (f, tl)) ty)

let t_let v t1 t2 =
  Hterm.hashcons (mk_term (Tlet (t1, (v, t2))) t2.t_ty)

let t_case t bl ty = Hterm.hashcons (mk_term (Tcase (t, bl)) ty)
let t_eps u f = Hterm.hashcons (mk_term (Teps (u, f)) u.vs_ty)

let t_label l t = Hterm.hashcons { t with t_label = l }
let t_label_add l t = Hterm.hashcons { t with t_label = l :: t.t_label }

(* hash-consing constructors for formulas *)

let mk_fmla n = { f_node = n; f_label = []; f_tag = -1 }
let f_app f tl = Hfmla.hashcons (mk_fmla (Fapp (f, tl)))
let f_quant q u f = Hfmla.hashcons (mk_fmla (Fquant (q, (u, f))))

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

let f_label l f = Hfmla.hashcons { f with f_label = l }
let f_label_add l f = Hfmla.hashcons { f with f_label = l :: f.f_label }

(* unsafe map with level *)

let brlvl fn lvl (pat, nv, t) = (pat, nv, fn (lvl + nv) t)

let map_term_unsafe fnT fnF lvl t = match t.t_node with
  | Tbvar _ | Tvar _ -> t
  | Tapp (f, tl) -> t_app f (List.map (fnT lvl) tl) t.t_ty
  | Tlet (t1, (u, t2)) -> t_let u (fnT lvl t1) (fnT (lvl + 1) t2)
  | Tcase (t1, bl) -> t_case (fnT lvl t1) (List.map (brlvl fnT lvl) bl) t.t_ty
  | Teps (u, f) -> t_eps u (fnF (lvl + 1) f)

let map_fmla_unsafe fnT fnF lvl f = match f.f_node with
  | Fapp (p, tl) -> f_app p (List.map (fnT lvl) tl)
  | Fquant (q, (u, f1)) -> f_quant q u (fnF (lvl + 1) f1)
  | Fbinop (op, f1, f2) -> f_binary op (fnF lvl f1) (fnF lvl f2)
  | Fnot f1 -> f_not (fnF lvl f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF lvl f1) (fnF lvl f2) (fnF lvl f3)
  | Flet (t, (u, f1)) -> f_let u (fnT lvl t) (fnF (lvl + 1) f1)
  | Fcase (t, bl) -> f_case (fnT lvl t) (List.map (brlvl fnF lvl) bl)

(* unsafe fold with level *)

let brlvl fn lvl acc (_, nv, t) = fn (lvl + nv) acc t

let fold_term_unsafe fnT fnF lvl acc t = match t.t_node with
  | Tbvar _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left (fnT lvl) acc tl
  | Tlet (t1, (u, t2)) -> fnT (lvl + 1) (fnT lvl acc t1) t2
  | Tcase (t1, bl) -> List.fold_left (brlvl fnT lvl) (fnT lvl acc t1) bl
  | Teps (u, f) -> fnF (lvl + 1) acc f

let fold_fmla_unsafe fnT fnF lvl acc f = match f.f_node with
  | Fapp (p, tl) -> List.fold_left (fnT lvl) acc tl
  | Fquant (q, (u, f1)) -> fnF (lvl + 1) acc f1
  | Fbinop (op, f1, f2) -> fnF lvl (fnF lvl acc f1) f2
  | Fnot f1 -> fnF lvl acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fnF lvl (fnF lvl (fnF lvl acc f1) f2) f3
  | Flet (t, (u, f1)) -> fnF (lvl + 1) (fnT lvl acc t) f1
  | Fcase (t, bl) -> List.fold_left (brlvl fnF lvl) (fnT lvl acc t) bl

exception FoldSkip

let forall_fnT prT lvl _ t = prT lvl t || raise FoldSkip
let forall_fnF prF lvl _ f = prF lvl f || raise FoldSkip
let exists_fnT prT lvl _ t = prT lvl t && raise FoldSkip
let exists_fnF prF lvl _ f = prF lvl f && raise FoldSkip

let forall_term_unsafe prT prF lvl t =
  try fold_term_unsafe (forall_fnT prT) (forall_fnF prF) lvl true t
  with FoldSkip -> false

let forall_fmla_unsafe prT prF lvl f =
  try fold_fmla_unsafe (forall_fnT prT) (forall_fnF prF) lvl true f
  with FoldSkip -> false

let exists_term_unsafe prT prF lvl t =
  try fold_term_unsafe (exists_fnT prT) (exists_fnF prF) lvl false t
  with FoldSkip -> true

let exists_fmla_unsafe prT prF lvl f =
  try fold_fmla_unsafe (exists_fnT prT) (exists_fnF prF) lvl false f
  with FoldSkip -> true

(* replaces variables with de Bruijn indices in term [t] using map [m] *)

let rec abst_term m lvl t = match t.t_node with
  | Tvar u ->
      (try t_bvar (Mvs.find u m + lvl) t.t_ty with Not_found -> t)
  | _ -> map_term_unsafe (abst_term m) (abst_fmla m) lvl t

and abst_fmla m lvl f = map_fmla_unsafe (abst_term m) (abst_fmla m) lvl f

let abst_term_single v t = abst_term (Mvs.add v 0 Mvs.empty) 0 t
let abst_fmla_single v f = abst_fmla (Mvs.add v 0 Mvs.empty) 0 f

(* replaces de Bruijn indices with variables in term [t] using map [m] *)

module Im = Map.Make(struct type t = int let compare = Pervasives.compare end)

let rec inst_term m lvl t = match t.t_node with
  | Tbvar n when n >= lvl ->
      (try t_var (Im.find (n - lvl) m) with Not_found -> assert false)
  | _ -> map_term_unsafe (inst_term m) (inst_fmla m) lvl t

and inst_fmla m lvl f = map_fmla_unsafe (inst_term m) (inst_fmla m) lvl f

let inst_term_single v t = inst_term (Im.add 0 v Im.empty) 0 t
let inst_fmla_single v f = inst_fmla (Im.add 0 v Im.empty) 0 f

(* looks for free de Bruijn indices *)

let rec closed_term lvl t = match t.t_node with
  | Tbvar x -> x < lvl
  | _ -> forall_term_unsafe closed_term closed_fmla lvl t

and closed_fmla lvl f = forall_fmla_unsafe closed_term closed_fmla lvl f

(* looks for occurrence of a variable from set [s] in a term [t] *)

let rec occurs_term s lvl t = match t.t_node with
  | Tvar u -> Svs.mem u s
  | _ -> exists_term_unsafe (occurs_term s) (occurs_fmla s) lvl t

and occurs_fmla s lvl f =
  exists_fmla_unsafe (occurs_term s) (occurs_fmla s) lvl f

let occurs_term_single v t = occurs_term (Svs.add v Svs.empty) 0 t
let occurs_fmla_single v f = occurs_fmla (Svs.add v Svs.empty) 0 f

let occurs_term s t = occurs_term s 0 t
let occurs_fmla s f = occurs_fmla s 0 f

(* replaces variables with terms in term [t] using map [m] *)

let rec subst_term m lvl t = match t.t_node with
  | Tvar u -> (try Mvs.find u m with Not_found -> t)
  | _ -> map_term_unsafe (subst_term m) (subst_fmla m) lvl t

and subst_fmla m lvl f = map_fmla_unsafe (subst_term m) (subst_fmla m) lvl f

let subst_term_single t1 v t =
  if v.vs_ty == t1.t_ty then subst_term (Mvs.add v t1 Mvs.empty) 0 t
                        else raise Ty.TypeMismatch

let subst_fmla_single t1 v f =
  if v.vs_ty == t1.t_ty then subst_fmla (Mvs.add v t1 Mvs.empty) 0 f
                        else raise Ty.TypeMismatch

let vt_check v t = if v.vs_ty == t.t_ty then () else raise Ty.TypeMismatch

let subst_term m t = let _ = Mvs.iter vt_check m in subst_term m 0 t
let subst_fmla m f = let _ = Mvs.iter vt_check m in subst_fmla m 0 f

(* set of free variables *)

let rec freevars_term lvl acc t = match t.t_node with
  | Tvar u -> Svs.add u acc
  | _ -> fold_term_unsafe freevars_term freevars_fmla lvl acc t

and freevars_fmla lvl acc t =
  fold_fmla_unsafe freevars_term freevars_fmla lvl acc t

let freevars_term t = freevars_term 0 Svs.empty t
let freevars_fmla f = freevars_fmla 0 Svs.empty f

(* USE PHYSICAL EQUALITY *)
(*
(* equality *)

let t_equal = (==)
let f_equal = (==)
*)

(* alpha-equivalence *)

let rec t_alpha_equal t1 t2 =
  t1 == t2 ||
  t1.t_ty == t2.t_ty &&
  match t1.t_node, t2.t_node with
    | Tbvar x1, Tbvar x2 ->
        x1 == x2
    | Tvar v1, Tvar v2 ->
        v1 == v2
    | Tapp (s1, l1), Tapp (s2, l2) ->
        (* assert (List.length l1 == List.length l2); *)
        s1 == s2 && List.for_all2 t_alpha_equal l1 l2
    | Tlet (t1, (v1, b1)), Tlet (t2, (v2, b2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_alpha_equal t1 t2 && t_alpha_equal b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        t_alpha_equal t1 t2 &&
        (try List.for_all2 tbranch_alpha_equal l1 l2
        with Invalid_argument _ -> false)
    | Teps (v1, f1), Teps (v2, f2) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        f_alpha_equal f1 f2
    | _ -> false

and f_alpha_equal f1 f2 =
  f1 == f2 ||
  match f1.f_node, f2.f_node with
    | Fapp (s1, l1), Fapp (s2, l2) ->
        (* assert (List.length l1 == List.length l2); *)
        s1 == s2 && List.for_all2 t_alpha_equal l1 l2
    | Fquant (q1, (v1, f1)), Fquant (q2, (v2, f2)) ->
        q1 == q2 && v1.vs_ty == v2.vs_ty && f_alpha_equal f1 f2
    | Fbinop (op1, f1, g1), Fbinop (op2, f2, g2) ->
        op1 == op2 && f_alpha_equal f1 f2 && f_alpha_equal g1 g2
    | Fnot f1, Fnot f2 ->
        f_alpha_equal f1 f2
    | Ftrue, Ftrue
    | Ffalse, Ffalse ->
        true
    | Fif (f1, g1, h1), Fif (f2, g2, h2) ->
        f_alpha_equal f1 f2 && f_alpha_equal g1 g2 && f_alpha_equal h1 h2
    | Flet (t1, (v1, f1)), Flet (t2, (v2, f2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_alpha_equal t1 t2 && f_alpha_equal f1 f2
    | Fcase (t1, l1), Fcase (t2, l2) ->
        t_alpha_equal t1 t2 &&
        (try List.for_all2 fbranch_alpha_equal l1 l2
        with Invalid_argument _ -> false)
    | _ -> false

and tbranch_alpha_equal (pat1, _, t1) (pat2, _, t2) =
  pat_alpha_equal pat1 pat2 && t_alpha_equal t1 t2

and fbranch_alpha_equal (pat1, _, f1) (pat2, _, f2) =
  pat_alpha_equal pat1 pat2 && f_alpha_equal f1 f2

(* matching modulo alpha in the pattern *)

exception NoMatch

let rec t_match s t1 t2 =
  if t1 == t2 then s else
  if t1.t_ty != t2.t_ty then raise NoMatch else
  match t1.t_node, t2.t_node with
    | Tbvar x1, Tbvar x2 when x1 == x2 ->
        s
    | Tvar v1, _ ->
        (try if Mvs.find v1 s == t2 then s else raise NoMatch
        with Not_found -> if closed_term 0 t2
          then Mvs.add v1 t2 s else raise NoMatch)
    | Tapp (s1, l1), Tapp (s2, l2) when s1 == s2 ->
        (* assert (List.length l1 == List.length l2); *)
        List.fold_left2 t_match s l1 l2
    | Tlet (t1, (v1, b1)), Tlet (t2, (v2, b2)) ->
        (* assert (v1.vs_ty == t1.t_ty && v2.vs_ty == t2.t_ty); *)
        t_match (t_match s t1 t2) b1 b2
    | Tcase (t1, l1), Tcase (t2, l2) ->
        (try List.fold_left2 tbranch_match (t_match s t1 t2) l1 l2
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
    | Fquant (q1, (v1, f1)), Fquant (q2, (v2, f2))
            when q1 == q2 && v1.vs_ty == v2.vs_ty ->
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
        (try List.fold_left2 fbranch_match (t_match s t1 t2) l1 l2
        with Invalid_argument _ -> raise NoMatch)
    | _ -> raise NoMatch

and tbranch_match s (pat1, _, t1) (pat2, _, t2) =
  if pat_alpha_equal pat1 pat2 then t_match s t1 t2 else raise NoMatch

and fbranch_match s (pat1, _, f1) (pat2, _, f2) =
  if pat_alpha_equal pat1 pat2 then f_match s f1 f2 else raise NoMatch

let t_match t1 t2 s = try Some (t_match s t1 t2) with NoMatch -> None
let f_match f1 f2 s = try Some (f_match s f1 f2) with NoMatch -> None

(* occurrence check *)

let rec t_occurs_term r lvl t = r == t ||
  exists_term_unsafe (t_occurs_term r) (t_occurs_fmla r) lvl t

and t_occurs_fmla r lvl f =
  exists_fmla_unsafe (t_occurs_term r) (t_occurs_fmla r) lvl f

let t_occurs_term r t = t_occurs_term r 0 t
let t_occurs_fmla r f = t_occurs_fmla r 0 f

let rec f_occurs_term r lvl t =
  exists_term_unsafe (f_occurs_term r) (f_occurs_fmla r) lvl t

and f_occurs_fmla r lvl f = r == f ||
  exists_fmla_unsafe (f_occurs_term r) (f_occurs_fmla r) lvl f

let f_occurs_term r t = f_occurs_term r 0 t
let f_occurs_fmla r f = f_occurs_fmla r 0 f

(* occurrence check modulo alpha *)

let rec t_alpha_occurs_term r lvl t = t_alpha_equal r t ||
  exists_term_unsafe (t_alpha_occurs_term r) (t_alpha_occurs_fmla r) lvl t

and t_alpha_occurs_fmla r lvl f =
  exists_fmla_unsafe (t_alpha_occurs_term r) (t_alpha_occurs_fmla r) lvl f

let t_alpha_occurs_term r t = t_alpha_occurs_term r 0 t
let t_alpha_occurs_fmla r f = t_alpha_occurs_fmla r 0 f

let rec f_alpha_occurs_term r lvl t =
  exists_term_unsafe (f_alpha_occurs_term r) (f_alpha_occurs_fmla r) lvl t

and f_alpha_occurs_fmla r lvl f = f_alpha_equal r f ||
  exists_fmla_unsafe (f_alpha_occurs_term r) (f_alpha_occurs_fmla r) lvl f

let f_alpha_occurs_term r t = f_alpha_occurs_term r 0 t
let f_alpha_occurs_fmla r f = f_alpha_occurs_fmla r 0 f

(* substitutes term [t1] for term [t2] in term [t] *)

let rec t_subst_term t1 t2 lvl t =
  if t == t2 then t1 else
  map_term_unsafe (t_subst_term t1 t2) (t_subst_fmla t1 t2) lvl t

and t_subst_fmla t1 t2 lvl f =
  map_fmla_unsafe (t_subst_term t1 t2) (t_subst_fmla t1 t2) lvl f

let t_subst_term t1 t2 t =
  if t1.t_ty == t2.t_ty then t_subst_term t1 t2 0 t
                        else raise Ty.TypeMismatch

let t_subst_fmla t1 t2 f =
  if t1.t_ty == t2.t_ty then t_subst_fmla t1 t2 0 f
                        else raise Ty.TypeMismatch

(* substitutes fmla [f1] for fmla [f2] in term [t] *)

let rec f_subst_term f1 f2 lvl t =
  map_term_unsafe (f_subst_term f1 f2) (f_subst_fmla f1 f2) lvl t

and f_subst_fmla f1 f2 lvl f =
  if f == f2 then f1 else
  map_fmla_unsafe (f_subst_term f1 f2) (f_subst_fmla f1 f2) lvl f

let f_subst_term f1 f2 t = f_subst_term f1 f2 0 t
let f_subst_fmla f1 f2 f = f_subst_fmla f1 f2 0 f

(* substitutes term [t1] for term [t2] in term [t] modulo alpha *)

let rec t_alpha_subst_term t1 t2 lvl t =
  if t == t2 then t1 else
  map_term_unsafe (t_alpha_subst_term t1 t2) (t_alpha_subst_fmla t1 t2) lvl t

and t_alpha_subst_fmla t1 t2 lvl f =
  map_fmla_unsafe (t_alpha_subst_term t1 t2) (t_alpha_subst_fmla t1 t2) lvl f

let t_alpha_subst_term t1 t2 t =
  if t1.t_ty == t2.t_ty then t_alpha_subst_term t1 t2 0 t
                        else raise Ty.TypeMismatch

let t_alpha_subst_fmla t1 t2 f =
  if t1.t_ty == t2.t_ty then t_alpha_subst_fmla t1 t2 0 f
                        else raise Ty.TypeMismatch

(* alpha_substitutes fmla [f1] for fmla [f2] in term [t] modulo alpha *)

let rec f_alpha_subst_term f1 f2 lvl t =
  map_term_unsafe (f_alpha_subst_term f1 f2) (f_alpha_subst_fmla f1 f2) lvl t

and f_alpha_subst_fmla f1 f2 lvl f =
  if f == f2 then f1 else
  map_fmla_unsafe (f_alpha_subst_term f1 f2) (f_alpha_subst_fmla f1 f2) lvl f

let f_alpha_subst_term f1 f2 t = f_alpha_subst_term f1 f2 0 t
let f_alpha_subst_fmla f1 f2 f = f_alpha_subst_fmla f1 f2 0 f

(* calculate the greatest free de Bruijn index *)

let ix_empty = (Mterm.empty, Mfmla.empty)

let max_ix_term mT lvl acc t = max acc (Mterm.find t mT - lvl)
let max_ix_fmla mF lvl acc f = max acc (Mfmla.find f mF - lvl)

let rec build_max_term lvl acc t = match t.t_node with
  | Tbvar ix -> let mT,mF = acc in (Mterm.add t ix mT, mF)
  | _ ->
      let mT,mF = fold_term_unsafe build_max_term build_max_fmla lvl acc t in
      let ix = fold_term_unsafe (max_ix_term mT) (max_ix_fmla mF) 0 (-1) t in
      (Mterm.add t ix mT, mF)

and build_max_fmla lvl acc f =
      let mT,mF = fold_fmla_unsafe build_max_term build_max_fmla lvl acc f in
      let ix = fold_fmla_unsafe (max_ix_term mT) (max_ix_fmla mF) 0 (-1) f in
      (mT, Mfmla.add f ix mF)

(* safe transparent map *)

let rec map_skip_term fnT fnF mT mF lvl t =
  if Mterm.find t mT < 0 then fnT t
  else  map_term_unsafe (map_skip_term fnT fnF mT mF)
                        (map_skip_fmla fnT fnF mT mF) lvl t

and map_skip_fmla fnT fnF mT mF lvl f =
  if Mfmla.find f mF < 0 then fnF f
  else  map_fmla_unsafe (map_skip_term fnT fnF mT mF)
                        (map_skip_fmla fnT fnF mT mF) lvl f

let map_skip_term fnT fnF lvl t =
  if lvl == 0 then fnT t
  else  let mT,mF = build_max_term lvl ix_empty t in
        map_skip_term fnT fnF mT mF lvl t

let map_skip_fmla fnT fnF lvl f =
  if lvl == 0 then fnF f
  else  let mT,mF = build_max_fmla lvl ix_empty f in
        map_skip_fmla fnT fnF mT mF lvl f

let map_trans_term fnT fnF t =
  map_term_unsafe (map_skip_term fnT fnF) (map_skip_fmla fnT fnF) 0 t

let map_trans_fmla fnT fnF f =
  map_fmla_unsafe (map_skip_term fnT fnF) (map_skip_fmla fnT fnF) 0 f

(* safe transparent fold *)

let rec fold_skip_term fnT fnF mT mF lvl acc t =
  if Mterm.find t mT < 0 then fnT acc t
  else fold_term_unsafe (fold_skip_term fnT fnF mT mF)
                        (fold_skip_fmla fnT fnF mT mF) lvl acc t

and fold_skip_fmla fnT fnF mT mF lvl acc f =
  if Mfmla.find f mF < 0 then fnF acc f
  else fold_fmla_unsafe (fold_skip_term fnT fnF mT mF)
                        (fold_skip_fmla fnT fnF mT mF) lvl acc f

let fold_skip_term fnT fnF lvl acc t =
  if lvl == 0 then fnT acc t
  else  let mT,mF = build_max_term lvl ix_empty t in
        fold_skip_term fnT fnF mT mF lvl acc t

let fold_skip_fmla fnT fnF lvl acc f =
  if lvl == 0 then fnF acc f
  else  let mT,mF = build_max_fmla lvl ix_empty f in
        fold_skip_fmla fnT fnF mT mF lvl acc f

let fold_trans_term fnT fnF acc t =
  fold_term_unsafe (fold_skip_term fnT fnF) (fold_skip_fmla fnT fnF) 0 acc t

let fold_trans_fmla fnT fnF acc f =
  fold_fmla_unsafe (fold_skip_term fnT fnF) (fold_skip_fmla fnT fnF) 0 acc f

let forall_fnT prT _ t = prT t || raise FoldSkip
let forall_fnF prF _ f = prF f || raise FoldSkip
let exists_fnT prT _ t = prT t && raise FoldSkip
let exists_fnF prF _ f = prF f && raise FoldSkip

let forall_trans_term prT prF t =
  try fold_trans_term (forall_fnT prT) (forall_fnF prF) true t
  with FoldSkip -> false

let forall_trans_fmla prT prF f =
  try fold_trans_fmla (forall_fnT prT) (forall_fnF prF) true f
  with FoldSkip -> false

let exists_trans_term prT prF t =
  try fold_trans_term (exists_fnT prT) (exists_fnF prF) false t
  with FoldSkip -> true

let exists_trans_fmla prT prF f =
  try fold_trans_fmla (exists_fnT prT) (exists_fnF prF) false f
  with FoldSkip -> true

(* smart constructors *)

let t_let v t1 t2 =
  if v.vs_ty == t1.t_ty then t_let v t1 (abst_term_single v t2)
                        else raise Ty.TypeMismatch

let f_let v t1 f2 =
  if v.vs_ty == t1.t_ty then f_let v t1 (abst_fmla_single v f2)
                        else raise Ty.TypeMismatch

let t_eps v f = t_eps v (abst_fmla_single v f)

let f_quant q v f = f_quant q v (abst_fmla_single v f)
let f_forall = f_quant Fforall
let f_exists = f_quant Fexists

let t_app f tl ty =
  let args, res = f.fs_scheme in
  let _ =
    try List.fold_left2 Ty.matching
        (Ty.matching Name.M.empty res ty)
        args (List.map (fun t -> t.t_ty) tl)
    with Invalid_argument _ -> raise BadArity
  in
  t_app f tl ty

let f_app p tl =
  let _ =
    try List.fold_left2 Ty.matching Name.M.empty
        p.ps_scheme (List.map (fun t -> t.t_ty) tl)
    with Invalid_argument _ -> raise BadArity
  in
  f_app p tl

let varmap_for_pattern p =
  let i = ref (-1) in
  let rec make acc p = match p.pat_node with
    | Pwild ->
        acc
    | Pvar n ->
        assert (not (Mvs.mem n acc));
        incr i; Mvs.add n !i acc
    | Papp (_, pl) ->
        List.fold_left make acc pl
    | Pas (p, n) ->
        assert (not (Mvs.mem n acc));
        incr i; make (Mvs.add n !i acc) p
  in
  let m = make Mvs.empty p in
  m, !i + 1

let t_case t bl ty =
  let make_tbranch (p, tbr) =
    if tbr.t_ty != ty then raise Ty.TypeMismatch else
    if p.pat_ty != t.t_ty then raise Ty.TypeMismatch else
    let m, nv = varmap_for_pattern p in (p, nv, abst_term m 0 tbr)
  in
  t_case t (List.map make_tbranch bl) ty

let f_case t bl =
  let make_fbranch (p, fbr) =
    if p.pat_ty != t.t_ty then raise Ty.TypeMismatch else
    let m, nv = varmap_for_pattern p in (p, nv, abst_fmla m 0 fbr)
  in
  f_case t (List.map make_fbranch bl)

(* opening binders *)

let open_bind_term (v, t) =
  let v = fresh_vsymbol v in v, inst_term_single v t

let open_bind_fmla (v, f) =
  let v = fresh_vsymbol v in v, inst_fmla_single v f

let rec rename_pat ns p = match p.pat_node with
  | Pwild ->
      p
  | Pvar n ->
      (try pat_var (Mvs.find n ns) with Not_found -> assert false)
  | Papp (f, pl) ->
      pat_app f (List.map (rename_pat ns) pl) p.pat_ty
  | Pas (p, n) ->
      pat_as (rename_pat ns p)
        (try Mvs.find n ns with Not_found -> assert false)

let substs_for_pattern pat =
  let m, _ = varmap_for_pattern pat in
  Mvs.fold
    (fun x i (vars, s, ns) ->
       let x' = fresh_vsymbol x in
       Svs.add x' vars, Im.add i x' s, Mvs.add x x' ns)
    m
    (Svs.empty, Im.empty, Mvs.empty)

let open_tbranch (pat, _, t) =
  let vars, s, ns = substs_for_pattern pat in
  (rename_pat ns pat, vars, inst_term s 0 t)

let open_fbranch (pat, _, f) =
  let vars, s, ns = substs_for_pattern pat in
  (rename_pat ns pat, vars, inst_fmla s 0 f)

(* safe opening map *)

let tbranch fn b = let pat,_,t = open_tbranch b in (pat, fn t)

let map_open_term fnT fnF t = match t.t_node with
  | Tbvar _ | Tvar _ -> t
  | Tapp (f, tl) -> t_app f (List.map fnT tl) t.t_ty
  | Tlet (t1, b) -> let u,t2 = open_bind_term b in t_let u (fnT t1) (fnT t2)
  | Tcase (t1, bl) -> t_case (fnT t1) (List.map (tbranch fnT) bl) t.t_ty
  | Teps b -> let u,f = open_bind_fmla b in t_eps u (fnF f)

let fbranch fn b = let pat,_,f = open_fbranch b in (pat, fn f)

let map_open_fmla fnT fnF f = match f.f_node with
  | Fapp (p, tl) -> f_app p (List.map fnT tl)
  | Fquant (q, b) -> let u,f1 = open_bind_fmla b in f_quant q u (fnF f1)
  | Fbinop (op, f1, f2) -> f_binary op (fnF f1) (fnF f2)
  | Fnot f1 -> f_not (fnF f1)
  | Ftrue | Ffalse -> f
  | Fif (f1, f2, f3) -> f_if (fnF f1) (fnF f2) (fnF f3)
  | Flet (t, b) -> let u,f1 = open_bind_fmla b in f_let u (fnT t) (fnF f1)
  | Fcase (t, bl) -> f_case (fnT t) (List.map (fbranch fnF) bl)

(* safe opening fold *)

let tbranch fn acc b = let _,_,t = open_tbranch b in fn acc t
let fbranch fn acc b = let _,_,f = open_fbranch b in fn acc f

let fold_open_term fnT fnF acc t = match t.t_node with
  | Tbvar _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left fnT acc tl
  | Tlet (t1, b) -> let _,t2 = open_bind_term b in fnT (fnT acc t1) t2
  | Tcase (t1, bl) -> List.fold_left (tbranch fnT) (fnT acc t1) bl
  | Teps b -> let _,f = open_bind_fmla b in fnF acc f

let fold_open_fmla fnT fnF acc f = match f.f_node with
  | Fapp (p, tl) -> List.fold_left fnT acc tl
  | Fquant (q, b) -> let _,f1 = open_bind_fmla b in fnF acc f1
  | Fbinop (op, f1, f2) -> fnF (fnF acc f1) f2
  | Fnot f1 -> fnF acc f1
  | Ftrue | Ffalse -> acc
  | Fif (f1, f2, f3) -> fnF (fnF (fnF acc f1) f2) f3
  | Flet (t, b) -> let _,f1 = open_bind_fmla b in fnF (fnT acc t) f1
  | Fcase (t, bl) -> List.fold_left (fbranch fnF) (fnT acc t) bl

let forall_open_term prT prF t =
  try fold_open_term (forall_fnT prT) (forall_fnF prF) true t
  with FoldSkip -> false

let forall_open_fmla prT prF f =
  try fold_open_fmla (forall_fnT prT) (forall_fnF prF) true f
  with FoldSkip -> false

let exists_open_term prT prF t =
  try fold_open_term (exists_fnT prT) (exists_fnF prF) false t
  with FoldSkip -> true

let exists_open_fmla prT prF f =
  try fold_open_fmla (exists_fnT prT) (exists_fnF prF) false f
  with FoldSkip -> true

