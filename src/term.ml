
type label 

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

  let rec equal_ty_node ty1 ty2 = match ty1, ty2 with
    | Tyvar n1, Tyvar n2 -> 
	Name.equal n1 n2
    | Tyapp (s1, l1), Tyapp (s2, l2) -> 
	equal_tysymbol s1 s2 && List.for_all2 equal_ty l1 l2
    | _ ->
	false

  and equal_ty = (==)

  let rec hash_ty_node = function
    | Tyvar v -> 
	Name.hash v
    | Tyapp (s, tl) -> 
	Hashcons.combine_list hash_ty (Name.hash s.ty_name) tl

  and hash_ty ty = 
    ty.ty_tag

  module Hty = Hashcons.Make(
    struct
      type node = ty_node
      let equal = equal_ty_node
      let hash = hash_ty_node
      type t = ty
      let node t = t.ty_node
    end)

  let mk_ty n t = { ty_node = n; ty_tag = t }
  let ty_var n = Hty.hashcons (Tyvar n) mk_ty
  let ty_app s tl = Hty.hashcons (Tyapp (s, tl)) mk_ty

end








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
