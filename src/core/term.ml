(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ident
open Ty

(** Variable symbols *)

type vsymbol = {
  vs_name : ident;
  vs_ty   : ty;
}

module Vsym = MakeMSHW (struct
  type t = vsymbol
  let tag vs = vs.vs_name.id_tag
end)

module Svs = Vsym.S
module Mvs = Vsym.M
module Hvs = Vsym.H
module Wvs = Vsym.W

let vs_equal : vsymbol -> vsymbol -> bool = (==)
let vs_hash vs = id_hash vs.vs_name
let vs_compare vs1 vs2 = id_compare vs1.vs_name vs2.vs_name

let create_vsymbol name ty = {
  vs_name = id_register name;
  vs_ty   = ty;
}

(** Function and predicate symbols *)

type lsymbol = {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
  ls_constr : int;
}

module Lsym = MakeMSHW (struct
  type t = lsymbol
  let tag ls = ls.ls_name.id_tag
end)

module Sls = Lsym.S
module Mls = Lsym.M
module Hls = Lsym.H
module Wls = Lsym.W

let ls_equal : lsymbol -> lsymbol -> bool = (==)
let ls_hash ls = id_hash ls.ls_name
let ls_compare ls1 ls2 = id_compare ls1.ls_name ls2.ls_name

let check_constr constr _args value =
  if constr = 0 || (constr > 0 && value <> None)
  then constr else invalid_arg "Term.create_lsymbol"

let create_lsymbol ?(constr=0) name args value = {
  ls_name   = id_register name;
  ls_args   = args;
  ls_value  = value;
  ls_constr = check_constr constr args value;
}

let create_fsymbol ?constr nm al vl =
  create_lsymbol ?constr nm al (Some vl)

let create_psymbol nm al =
  create_lsymbol ~constr:0 nm al None

let ls_ty_freevars ls =
  let acc = oty_freevars Stv.empty ls.ls_value in
  List.fold_left ty_freevars acc ls.ls_args

(** Patterns *)

type pattern = {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty   : ty;
}

and pattern_node =
  | Pwild (* _ *)
  | Pvar of vsymbol (* newly introduced variables *)
  | Papp of lsymbol * pattern list (* application *)
  | Por  of pattern * pattern (* | *)
  | Pas  of pattern * vsymbol
  (* naming a term recognized by pattern as a variable *)

(* h-consing constructors for patterns *)

let mk_pattern n vs ty = {
  pat_node = n;
  pat_vars = vs;
  pat_ty   = ty;
}

exception UncoveredVar of vsymbol
exception DuplicateVar of vsymbol

let pat_wild ty = mk_pattern Pwild Svs.empty ty
let pat_var v   = mk_pattern (Pvar v) (Svs.singleton v) v.vs_ty

let pat_as p v =
  let s = Svs.add_new (DuplicateVar v) v p.pat_vars in
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

let pat_map fn = pat_map (fun p ->
  let res = fn p in ty_equal_check p.pat_ty res.pat_ty; res)

let pat_fold fn acc pat = match pat.pat_node with
  | Pwild | Pvar _ -> acc
  | Papp (_, pl) -> List.fold_left fn acc pl
  | Pas (p, _) -> fn acc p
  | Por (p, q) -> fn (fn acc p) q

let pat_all pr pat = Util.all pat_fold pr pat
let pat_any pr pat = Util.any pat_fold pr pat

(* smart constructors for patterns *)

exception BadArity of lsymbol * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol

let pat_app fs pl ty =
  let s = match fs.ls_value with
    | Some vty -> ty_match Mtv.empty vty ty
    | None -> raise (FunctionSymbolExpected fs)
  in
  let mtch s ty p = ty_match s ty p.pat_ty in
  ignore (try List.fold_left2 mtch s fs.ls_args pl with
    | Invalid_argument _ -> raise (BadArity (fs, List.length pl)));
  if fs.ls_constr = 0 then raise (ConstructorExpected fs);
  pat_app fs pl ty

let pat_as p v =
  ty_equal_check p.pat_ty v.vs_ty;
  pat_as p v

let pat_or p q =
  ty_equal_check p.pat_ty q.pat_ty;
  pat_or p q

(* rename all variables in a pattern *)

let rec pat_rename_all m p = match p.pat_node with
  | Pvar v -> pat_var (Mvs.find v m)
  | Pas (p, v) -> pat_as (pat_rename_all m p) (Mvs.find v m)
  | _ -> pat_map (pat_rename_all m) p

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
  | Tforall
  | Texists

type binop =
  | Tand
  | Tor
  | Timplies
  | Tiff

type term = {
  t_node  : term_node;
  t_ty    : ty option;
  t_attrs : Sattr.t;
  t_loc   : Loc.position option;
}

and term_node =
  | Tvar of vsymbol
  | Tconst of Number.constant
  | Tapp of lsymbol * term list
  | Tif of term * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of term_bound
  | Tquant of quant * term_quant
  | Tbinop of binop * term * term
  | Tnot of term
  | Ttrue
  | Tfalse

and term_bound  = vsymbol * bind_info * term
and term_branch = pattern * bind_info * term
and term_quant  = vsymbol list * bind_info * trigger * term

and trigger = term list list

and bind_info = {
  bv_vars  : int Mvs.t;   (* free variables *)
  bv_subst : term Mvs.t   (* deferred substitution *)
}

(* term equality modulo alpha-equivalence and location *)

exception CompLT
exception CompGT

type frame = int Mvs.t * term Mvs.t

type term_or_bound =
  | Trm of term * frame list
  | Bnd of int

let rec descend vml t = match t.t_node with
  | Tvar vs ->
      let rec find vs = function
        | (bv,vm)::vml ->
            begin match Mvs.find_opt vs bv with
            | Some i -> Bnd i
            | None ->
                begin match Mvs.find_opt vs vm with
                | Some t -> descend vml t
                | None   -> find vs vml
                end
            end
        | [] -> Trm (t, [])
      in
      find vs vml
  | _ -> Trm (t, vml)

let t_compare trigger attr t1 t2 =
  let comp_raise c =
    if c < 0 then raise CompLT else if c > 0 then raise CompGT in
  let perv_compare h1 h2 = comp_raise (Pervasives.compare h1 h2) in
  let rec pat_compare (bnd,bv1,bv2 as state) p1 p2 =
    match p1.pat_node, p2.pat_node with
    | Pwild, Pwild ->
        bnd, bv1, bv2
    | Pvar v1, Pvar v2 ->
        bnd + 1, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2
    | Papp (s1, l1), Papp (s2, l2) ->
        comp_raise (ls_compare s1 s2);
        List.fold_left2 pat_compare state l1 l2
    | Por (p1, q1), Por (p2, q2) ->
        let (_,bv1,bv2 as res) = pat_compare state p1 p2 in
        let rec or_cmp q1 q2 = match q1.pat_node, q2.pat_node with
          | Pwild, Pwild -> ()
          | Pvar v1, Pvar v2 ->
              perv_compare (Mvs.find v1 bv1) (Mvs.find v2 bv2)
          | Papp (s1, l1), Papp (s2, l2) ->
              comp_raise (ls_compare s1 s2);
              List.iter2 or_cmp l1 l2
          | Por (p1, q1), Por (p2, q2) ->
              or_cmp p1 p2; or_cmp q1 q2
          | Pas (p1, v1), Pas (p2, v2) ->
              or_cmp p1 p2;
              perv_compare (Mvs.find v1 bv1) (Mvs.find v2 bv2)
          | Pwild,  _ -> raise CompLT | _, Pwild  -> raise CompGT
          | Pvar _, _ -> raise CompLT | _, Pvar _ -> raise CompGT
          | Papp _, _ -> raise CompLT | _, Papp _ -> raise CompGT
          | Por _,  _ -> raise CompLT | _, Por _  -> raise CompGT
        in
        or_cmp q1 q2;
        res
    | Pas (p1, v1), Pas (p2, v2) ->
        let bnd, bv1, bv2 = pat_compare state p1 p2 in
        bnd + 1, Mvs.add v1 bnd bv1, Mvs.add v2 bnd bv2
    | Pwild, _  -> raise CompLT | _, Pwild  -> raise CompGT
    | Pvar _, _ -> raise CompLT | _, Pvar _ -> raise CompGT
    | Papp _, _ -> raise CompLT | _, Papp _ -> raise CompGT
    | Por _, _  -> raise CompLT | _, Por _  -> raise CompGT
  in
  let rec t_compare bnd vml1 vml2 t1 t2 =
    if t1 != t2 || vml1 <> [] || vml2 <> [] then begin
      comp_raise (oty_compare t1.t_ty t2.t_ty);
      if attr then comp_raise (Sattr.compare t1.t_attrs t2.t_attrs) else ();
      match descend vml1 t1, descend vml2 t2 with
      | Bnd i1, Bnd i2 -> perv_compare i1 i2
      | Bnd _, Trm _ -> raise CompLT
      | Trm _, Bnd _ -> raise CompGT
      | Trm (t1,vml1), Trm (t2,vml2) ->
          begin match t1.t_node, t2.t_node with
          | Tvar v1, Tvar v2 ->
              comp_raise (vs_compare v1 v2)
          | Tconst c1, Tconst c2 ->
              let open Number in
              begin match c1, c2 with
              | ConstInt { ic_negative = s1; ic_abs = IConstRaw b1 },
                ConstInt { ic_negative = s2; ic_abs = IConstRaw b2 } ->
                  perv_compare s1 s2;
                  comp_raise (BigInt.compare b1 b2)
              | _, _ -> perv_compare c1 c2
              end
          | Tapp (s1,l1), Tapp (s2,l2) ->
              comp_raise (ls_compare s1 s2);
              List.iter2 (t_compare bnd vml1 vml2) l1 l2
          | Tif (f1,t1,e1), Tif (f2,t2,e2) ->
              t_compare bnd vml1 vml2 f1 f2;
              t_compare bnd vml1 vml2 t1 t2;
              t_compare bnd vml1 vml2 e1 e2
          | Tlet (t1,(v1,b1,e1)), Tlet (t2,(v2,b2,e2)) ->
              t_compare bnd vml1 vml2 t1 t2;
              let vml1 = (Mvs.singleton v1 bnd, b1.bv_subst) :: vml1 in
              let vml2 = (Mvs.singleton v2 bnd, b2.bv_subst) :: vml2 in
              t_compare (bnd + 1) vml1 vml2 e1 e2
          | Tcase (t1,bl1), Tcase (t2,bl2) ->
              t_compare bnd vml1 vml2 t1 t2;
              let b_compare (p1,b1,t1) (p2,b2,t2) =
                let bnd,bv1,bv2 = pat_compare (bnd,Mvs.empty,Mvs.empty) p1 p2 in
                let vml1 = (bv1, b1.bv_subst) :: vml1 in
                let vml2 = (bv2, b2.bv_subst) :: vml2 in
                t_compare bnd vml1 vml2 t1 t2; 0 in
              comp_raise (Lists.compare b_compare bl1 bl2)
          | Teps (v1,b1,e1), Teps (v2,b2,e2) ->
              let vml1 = (Mvs.singleton v1 bnd, b1.bv_subst) :: vml1 in
              let vml2 = (Mvs.singleton v2 bnd, b2.bv_subst) :: vml2 in
              t_compare (bnd + 1) vml1 vml2 e1 e2
          | Tquant (q1,(vl1,b1,tr1,f1)), Tquant (q2,(vl2,b2,tr2,f2)) ->
              perv_compare q1 q2;
              let rec add bnd bv1 bv2 vl1 vl2 = match vl1, vl2 with
                | (v1::vl1), (v2::vl2) ->
                    let bv1 = Mvs.add v1 bnd bv1 in
                    let bv2 = Mvs.add v2 bnd bv2 in
                    add (bnd + 1) bv1 bv2 vl1 vl2
                | [], (_::_) -> raise CompLT
                | (_::_), [] -> raise CompGT
                | [], [] -> bnd, bv1, bv2 in
              let bnd, bv1, bv2 = add bnd Mvs.empty Mvs.empty vl1 vl2 in
              let vml1 = (bv1, b1.bv_subst) :: vml1 in
              let vml2 = (bv2, b2.bv_subst) :: vml2 in
              let tr_cmp t1 t2 = t_compare bnd vml1 vml2 t1 t2; 0 in
              if trigger then comp_raise (Lists.compare (Lists.compare tr_cmp) tr1 tr2) else ();
              t_compare bnd vml1 vml2 f1 f2
          | Tbinop (op1,f1,g1), Tbinop (op2,f2,g2) ->
              perv_compare op1 op2;
              t_compare bnd vml1 vml2 f1 f2;
              t_compare bnd vml1 vml2 g1 g2
          | Tnot f1, Tnot f2 ->
              t_compare bnd vml1 vml2 f1 f2
          | Ttrue, Ttrue -> ()
          | Tfalse, Tfalse -> ()
          | Tvar _, _   -> raise CompLT | _, Tvar _   -> raise CompGT
          | Tconst _, _ -> raise CompLT | _, Tconst _ -> raise CompGT
          | Tapp _, _   -> raise CompLT | _, Tapp _   -> raise CompGT
          | Tif _, _    -> raise CompLT | _, Tif _    -> raise CompGT
          | Tlet _, _   -> raise CompLT | _, Tlet _   -> raise CompGT
          | Tcase _, _  -> raise CompLT | _, Tcase _  -> raise CompGT
          | Teps _, _   -> raise CompLT | _, Teps _   -> raise CompGT
          | Tquant _, _ -> raise CompLT | _, Tquant _ -> raise CompGT
          | Tbinop _, _ -> raise CompLT | _, Tbinop _ -> raise CompGT
          | Tnot _, _   -> raise CompLT | _, Tnot _   -> raise CompGT
          | Ttrue, _    -> raise CompLT | _, Ttrue    -> raise CompGT
          end
    end in
  try t_compare 0 [] [] t1 t2; 0
  with CompLT -> -1 | CompGT -> 1

let t_equal t1 t2 = (t_compare true true t1 t2 = 0)

let t_equal_nt_na t1 t2 = (t_compare false false t1 t2 = 0)

let t_compare = t_compare true true

let t_similar t1 t2 =
  oty_equal t1.t_ty t2.t_ty &&
  match t1.t_node, t2.t_node with
    | Tvar v1, Tvar v2 -> vs_equal v1 v2
    | Tconst c1, Tconst c2 -> c1 = c2
    | Tapp (s1,l1), Tapp (s2,l2) -> ls_equal s1 s2 && Lists.equal (==) l1 l2
    | Tif (f1,t1,e1), Tif (f2,t2,e2) -> f1 == f2 && t1 == t2 && e1 == e2
    | Tlet (t1,bv1), Tlet (t2,bv2) -> t1 == t2 && bv1 == bv2
    | Tcase (t1,bl1), Tcase (t2,bl2) -> t1 == t2 && Lists.equal (==) bl1 bl2
    | Teps bv1, Teps bv2 -> bv1 == bv2
    | Tquant (q1,bv1), Tquant (q2,bv2) -> q1 = q2 && bv1 == bv2
    | Tbinop (o1,f1,g1), Tbinop (o2,f2,g2) -> o1 = o2 && f1 == f2 && g1 == g2
    | Tnot f1, Tnot f2 -> f1 == f2
    | Ttrue, Ttrue | Tfalse, Tfalse -> true
    | _, _ -> false

let t_hash trigger attr t =
  let rec pat_hash bnd bv p = match p.pat_node with
    | Pwild -> bnd, bv, 0
    | Pvar v -> bnd + 1, Mvs.add v bnd bv, bnd + 1
    | Papp (s,l) ->
        let hash (bnd,bv,h) p =
          let bnd,bv,hp = pat_hash bnd bv p in
          bnd, bv, Hashcons.combine h hp in
        List.fold_left hash (bnd,bv,ls_hash s) l
    | Por (p,q) ->
        let bnd,bv,hp = pat_hash bnd bv p in
        let rec or_hash q = match q.pat_node with
          | Pwild -> 0
          | Pvar v -> Mvs.find v bv + 1
          | Papp (s,l) -> Hashcons.combine_list or_hash (ls_hash s) l
          | Por (p,q) -> Hashcons.combine (or_hash p) (or_hash q)
          | Pas (p,v) -> Hashcons.combine (or_hash p) (Mvs.find v bv + 1)
        in
        bnd, bv, Hashcons.combine hp (or_hash q)
    | Pas (p,v) ->
        let bnd,bv,hp = pat_hash bnd bv p in
        bnd + 1, Mvs.add v bnd bv, Hashcons.combine hp (bnd + 1)
  in
  let rec t_hash bnd vml t =
    let h = oty_hash t.t_ty in
    let h =
      if attr then
        let comb l h = Hashcons.combine (attr_hash l) h in
        Sattr.fold comb t.t_attrs h
      else h
    in
    Hashcons.combine h
      begin match descend vml t with
      | Bnd i -> i + 1
      | Trm (t,vml) ->
          begin match t.t_node with
          | Tvar v -> vs_hash v
          | Tconst c -> Hashtbl.hash c
          | Tapp (s,l) ->
              Hashcons.combine_list (t_hash bnd vml) (ls_hash s) l
          | Tif (f,t,e) ->
              let hf = t_hash bnd vml f in
              let ht = t_hash bnd vml t in
              let he = t_hash bnd vml e in
              Hashcons.combine2 hf ht he
          | Tlet (t,(v,b,e)) ->
              let h = t_hash bnd vml t in
              let vml = (Mvs.singleton v bnd, b.bv_subst) :: vml in
              Hashcons.combine h (t_hash (bnd + 1) vml e)
          | Tcase (t,bl) ->
              let h = t_hash bnd vml t in
              let b_hash (p,b,t) =
                let bnd,bv,hp = pat_hash bnd Mvs.empty p in
                let vml = (bv, b.bv_subst) :: vml in
                Hashcons.combine hp (t_hash bnd vml t) in
              Hashcons.combine_list b_hash h bl
          | Teps (v,b,e) ->
              let vml = (Mvs.singleton v bnd, b.bv_subst) :: vml in
              t_hash (bnd + 1) vml e
          | Tquant (q,(vl,b,tr,f)) ->
              let h = Hashtbl.hash q in
              let rec add bnd bv vl = match vl with
                | v::vl -> add (bnd + 1) (Mvs.add v bnd bv) vl
                | [] -> bnd, bv in
              let bnd, bv = add bnd Mvs.empty vl in
              let vml = (bv, b.bv_subst) :: vml in
              let h =
                if trigger then
                  List.fold_left
                    (Hashcons.combine_list (t_hash bnd vml)) h tr
                else h
              in
              Hashcons.combine h (t_hash bnd vml f)
          | Tbinop (op,f,g) ->
              let ho = Hashtbl.hash op in
              let hf = t_hash bnd vml f in
              let hg = t_hash bnd vml g in
              Hashcons.combine2 ho hf hg
          | Tnot f ->
              Hashcons.combine 1 (t_hash bnd vml f)
          | Ttrue -> 2
          | Tfalse -> 3
          end
    end in
  t_hash 0 [] t

(* type checking *)

exception TermExpected of term
exception FmlaExpected of term

let t_type t = match t.t_ty with
  | Some ty -> ty
  | None -> raise (TermExpected t)

let t_prop f =
  if f.t_ty = None then f else raise (FmlaExpected f)

let t_ty_check t ty = match ty, t.t_ty with
  | Some l, Some r -> ty_equal_check l r
  | Some _, None -> raise (TermExpected t)
  | None, Some _ -> raise (FmlaExpected t)
  | None, None -> ()

let vs_check v t = ty_equal_check v.vs_ty (t_type t)

(* trigger equality and traversal *)

let tr_equal = Lists.equal (Lists.equal t_equal)

let tr_map fn = List.map (List.map fn)
let tr_fold fn = List.fold_left (List.fold_left fn)
let tr_map_fold fn = Lists.map_fold_left (Lists.map_fold_left fn)

(* bind_info equality, hash, and traversal *)

let bnd_map fn bv = { bv with bv_subst = Mvs.map fn bv.bv_subst }

let bnd_fold fn acc bv = Mvs.fold (fun _ t a -> fn a t) bv.bv_subst acc

let bnd_map_fold fn acc bv =
  let acc,s = Mvs.mapi_fold (fun _ t a -> fn a t) bv.bv_subst acc in
  acc, { bv with bv_subst = s }

(* hash-consing for terms and formulas *)

let vars_union s1 s2 = Mvs.union (fun _ m n -> Some (m + n)) s1 s2

let add_b_vars s (_,b,_) = vars_union s b.bv_vars

let rec t_vars t = match t.t_node with
  | Tvar v -> Mvs.singleton v 1
  | Tconst _ -> Mvs.empty
  | Tapp (_,tl) -> List.fold_left add_t_vars Mvs.empty tl
  | Tif (f,t,e) -> add_t_vars (add_t_vars (t_vars f) t) e
  | Tlet (t,bt) -> add_b_vars (t_vars t) bt
  | Tcase (t,bl) -> List.fold_left add_b_vars (t_vars t) bl
  | Teps (_,b,_) -> b.bv_vars
  | Tquant (_,(_,b,_,_)) -> b.bv_vars
  | Tbinop (_,f1,f2) -> add_t_vars (t_vars f1) f2
  | Tnot f -> t_vars f
  | Ttrue | Tfalse -> Mvs.empty

and add_t_vars s t = vars_union s (t_vars t)

let add_nt_vars _ n t s = vars_union s
  (if n = 1 then t_vars t else Mvs.map (( * ) n) (t_vars t))

module TermOHT = struct
  type t = term
  let hash = t_hash true true
  let equal = t_equal
  let compare = t_compare
end

module Mterm = Extmap.Make(TermOHT)
module Sterm = Extset.MakeOfMap(Mterm)
module Hterm = Exthtbl.Make(TermOHT)

module TermOHT_nt_na = struct
  type t = term
  let hash = t_hash false false
  let equal = t_equal_nt_na
end

module Hterm_nt_na = Exthtbl.Make(TermOHT_nt_na)

let t_hash = t_hash true true

(* hash-consing constructors for terms *)

let mk_term n ty = {
  t_node  = n;
  t_attrs = Sattr.empty;
  t_loc   = None;
  t_ty    = ty;
}

let t_var v         = mk_term (Tvar v) (Some v.vs_ty)
let t_const c ty    = mk_term (Tconst c) (Some ty)
let t_app f tl ty   = mk_term (Tapp (f, tl)) ty
let t_if f t1 t2    = mk_term (Tif (f, t1, t2)) t2.t_ty
let t_let t1 bt ty  = mk_term (Tlet (t1, bt)) ty
let t_case t1 bl ty = mk_term (Tcase (t1, bl)) ty
let t_eps bf ty     = mk_term (Teps bf) ty
let t_quant q qf    = mk_term (Tquant (q, qf)) None
let t_binary op f g = mk_term (Tbinop (op, f, g)) None
let t_not f         = mk_term (Tnot f) None
let t_true          = mk_term (Ttrue) None
let t_false         = mk_term (Tfalse) None

let t_attr_set ?loc l t = { t with t_attrs = l; t_loc = loc }

let t_attr_add l t = { t with t_attrs = Sattr.add l t.t_attrs }

let t_attr_remove l t = { t with t_attrs = Sattr.remove l t.t_attrs }

let t_attr_copy s t =
  if s == t then s else
  if t_similar s t && Sattr.is_empty t.t_attrs && t.t_loc = None then s else
  let attrs = Sattr.union s.t_attrs t.t_attrs in
  let loc = if t.t_loc = None then s.t_loc else t.t_loc in
  { t with t_attrs = attrs; t_loc = loc }

(* unsafe map *)

let bound_map fn (u,b,e) = (u, bnd_map fn b, fn e)

let t_map_unsafe fn t = t_attr_copy t (match t.t_node with
  | Tvar _ | Tconst _ -> t
  | Tapp (f,tl) -> t_app f (List.map fn tl) t.t_ty
  | Tif (f,t1,t2) -> t_if (fn f) (fn t1) (fn t2)
  | Tlet (e,b) -> t_let (fn e) (bound_map fn b) t.t_ty
  | Tcase (e,bl) -> t_case (fn e) (List.map (bound_map fn) bl) t.t_ty
  | Teps b -> t_eps (bound_map fn b) t.t_ty
  | Tquant (q,(vl,b,tl,f)) -> t_quant q (vl, bnd_map fn b, tr_map fn tl, fn f)
  | Tbinop (op,f1,f2) -> t_binary op (fn f1) (fn f2)
  | Tnot f1 -> t_not (fn f1)
  | Ttrue | Tfalse -> t)

(* unsafe fold *)

let bound_fold fn acc (_,b,e) = fn (bnd_fold fn acc b) e

let t_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ -> acc
  | Tapp (_,tl) -> List.fold_left fn acc tl
  | Tif (f,t1,t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (e,b) -> fn (bound_fold fn acc b) e
  | Tcase (e,bl) -> List.fold_left (bound_fold fn) (fn acc e) bl
  | Teps b -> bound_fold fn acc b
  | Tquant (_,(_,b,tl,f1)) -> fn (tr_fold fn (bnd_fold fn acc b) tl) f1
  | Tbinop (_,f1,f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc

(* unsafe map_fold *)

let bound_map_fold fn acc (u,b,e) =
  let acc, b = bnd_map_fold fn acc b in
  let acc, e = fn acc e in
  acc, (u,b,e)

let t_map_fold_unsafe fn acc t = match t.t_node with
  | Tvar _ | Tconst _ ->
      acc, t
  | Tapp (f,tl) ->
      let acc,sl = Lists.map_fold_left fn acc tl in
      acc, t_attr_copy t (t_app f sl t.t_ty)
  | Tif (f,t1,t2) ->
      let acc, g  = fn acc f in
      let acc, s1 = fn acc t1 in
      let acc, s2 = fn acc t2 in
      acc, t_attr_copy t (t_if g s1 s2)
  | Tlet (e,b) ->
      let acc, e = fn acc e in
      let acc, b = bound_map_fold fn acc b in
      acc, t_attr_copy t (t_let e b t.t_ty)
  | Tcase (e,bl) ->
      let acc, e = fn acc e in
      let acc, bl = Lists.map_fold_left (bound_map_fold fn) acc bl in
      acc, t_attr_copy t (t_case e bl t.t_ty)
  | Teps b ->
      let acc, b = bound_map_fold fn acc b in
      acc, t_attr_copy t (t_eps b t.t_ty)
  | Tquant (q,(vl,b,tl,f1)) ->
      let acc, b = bnd_map_fold fn acc b in
      let acc, tl = tr_map_fold fn acc tl in
      let acc, f1 = fn acc f1 in
      acc, t_attr_copy t (t_quant q (vl,b,tl,f1))
  | Tbinop (op,f1,f2) ->
      let acc, g1 = fn acc f1 in
      let acc, g2 = fn acc f2 in
      acc, t_attr_copy t (t_binary op g1 g2)
  | Tnot f1 ->
      let acc, g1 = fn acc f1 in
      acc, t_attr_copy t (t_not g1)
  | Ttrue | Tfalse ->
      acc, t

(* type-unsafe term substitution *)

let rec t_subst_unsafe m t =
  let t_subst t = t_subst_unsafe m t in
  let b_subst (u,b,e as bv) =
    if Mvs.set_disjoint m b.bv_vars then bv else
    (u, bv_subst_unsafe m b, e) in
  match t.t_node with
  | Tvar u ->
      t_attr_copy t (Mvs.find_def t u m)
  | Tlet (e, bt) ->
      let d = t_subst e in
      t_attr_copy t (t_let d (b_subst bt) t.t_ty)
  | Tcase (e, bl) ->
      let d = t_subst e in
      let bl = List.map b_subst bl in
      t_attr_copy t (t_case d bl t.t_ty)
  | Teps bf ->
      t_attr_copy t (t_eps (b_subst bf) t.t_ty)
  | Tquant (q, (vl,b,tl,f1 as bq)) ->
      let bq =
        if Mvs.set_disjoint m b.bv_vars then bq else
        (vl,bv_subst_unsafe m b,tl,f1) in
      t_attr_copy t (t_quant q bq)
  | _ ->
      t_map_unsafe t_subst t

and bv_subst_unsafe m b =
  (* restrict m to the variables free in b *)
  let m = Mvs.set_inter m b.bv_vars in
  (* if m is empty, return early *)
  if Mvs.is_empty m then b else
  (* remove from b.bv_vars the variables replaced by m *)
  let s = Mvs.set_diff b.bv_vars m in
  (* add to b.bv_vars the free variables added by m *)
  let s = Mvs.fold2_inter add_nt_vars b.bv_vars m s in
  (* apply m to the terms in b.bv_subst *)
  let h = Mvs.map (t_subst_unsafe m) b.bv_subst in
  (* join m to b.bv_subst *)
  let h = Mvs.set_union h m in
  (* reconstruct b *)
  { bv_vars = s ; bv_subst = h }

let t_subst_unsafe m t =
  if Mvs.is_empty m then t else t_subst_unsafe m t

(* close bindings *)

let bnd_new s = { bv_vars = s ; bv_subst = Mvs.empty }

let t_close_bound v t = (v, bnd_new (Mvs.remove v (t_vars t)), t)

let t_close_branch p t = (p, bnd_new (Mvs.set_diff (t_vars t) p.pat_vars), t)

let t_close_quant vl tl f =
  let del_v s v = Mvs.remove v s in
  let s = tr_fold add_t_vars (t_vars f) tl in
  let s = List.fold_left del_v s vl in
  (vl, bnd_new s, tl, t_prop f)

(* open bindings *)

let fresh_vsymbol v =
  create_vsymbol (id_clone v.vs_name) v.vs_ty

let vs_rename h v =
  let u = fresh_vsymbol v in
  Mvs.add v (t_var u) h, u

let vl_rename h vl =
  Lists.map_fold_left vs_rename h vl

let pat_rename h p =
  let add_vs v () = fresh_vsymbol v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_rename_all m p in
  Mvs.union (fun _ _ t -> Some t) h (Mvs.map t_var m), p

let t_open_bound (v,b,t) =
  let m,v = vs_rename b.bv_subst v in
  v, t_subst_unsafe m t

let t_open_bound_with e (v,b,t) =
  vs_check v e;
  let m = Mvs.add v e b.bv_subst in
  t_subst_unsafe m t

let t_open_branch (p,b,t) =
  let m,p = pat_rename b.bv_subst p in
  p, t_subst_unsafe m t

let t_open_quant (vl,b,tl,f) =
  let m,vl = vl_rename b.bv_subst vl in
  let tl = tr_map (t_subst_unsafe m) tl in
  vl, tl, t_subst_unsafe m f

let t_clone_bound_id (v,_,_) = id_clone v.vs_name

(** open bindings with optimized closing callbacks *)

let t_open_bound_cb tb =
  let v, t = t_open_bound tb in
  let close v' t' =
    if t == t' && vs_equal v v' then tb else t_close_bound v' t'
  in
  v, t, close

let t_open_branch_cb tbr =
  let p, t = t_open_branch tbr in
  let close p' t' =
    if t == t' && p == p' then tbr else t_close_branch p' t'
  in
  p, t, close

let t_open_quant_cb fq =
  let vl, tl, f = t_open_quant fq in
  let close vl' tl' f' =
    if f == f' &&
      Lists.equal (Lists.equal ((==) : term -> term -> bool)) tl tl' &&
      Lists.equal vs_equal vl vl'
    then fq else t_close_quant vl' tl' f'
  in
  vl, tl, f, close

(* constructors with type checking *)

let ls_arg_inst ls tl =
  let mtch s ty t = ty_match s ty (t_type t) in
  try List.fold_left2 mtch Mtv.empty ls.ls_args tl with
    | Invalid_argument _ -> raise (BadArity (ls, List.length tl))

let ls_app_inst ls tl ty =
  let s = ls_arg_inst ls tl in
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> ty_match s vty ty
    | None, None -> s

let t_app_infer ls tl =
  let s = ls_arg_inst ls tl in
  t_app ls tl (oty_inst s ls.ls_value)

let t_app ls tl ty = ignore (ls_app_inst ls tl ty); t_app ls tl ty

let fs_app fs tl ty = t_app fs tl (Some ty)
let ps_app ps tl    = t_app ps tl None

let t_nat_const n =
  assert (n >= 0);
  t_const (Number.const_of_int n) ty_int

let t_bigint_const n = t_const (Number.const_of_big_int n) Ty.ty_int

exception InvalidIntegerLiteralType of ty
exception InvalidRealLiteralType of ty

let check_literal c ty =
  let ts = match ty.ty_node with
    | Tyapp (ts,[]) -> ts
    | _ -> match c with
           | Number.ConstInt _ -> raise (InvalidIntegerLiteralType ty)
           | Number.ConstReal _ -> raise (InvalidRealLiteralType ty)
  in
  match c with
  | Number.ConstInt _ when ts_equal ts ts_int -> ()
  | Number.ConstInt n ->
     begin match ts.ts_def with
           | Range ir -> Number.(check_range n ir)
           | _ -> raise (InvalidIntegerLiteralType ty)
     end
  | Number.ConstReal _ when ts_equal ts ts_real -> ()
  | Number.ConstReal x ->
     begin match ts.ts_def with
           | Float fp -> Number.(check_float x.Number.rc_abs fp)
           | _ -> raise (InvalidRealLiteralType ty)
     end

let t_const c ty = check_literal c ty; t_const c ty

let t_if f t1 t2 =
  t_ty_check t2 t1.t_ty;
  t_if (t_prop f) t1 t2

let t_let t1 ((v,_,t2) as bt) =
  vs_check v t1;
  t_let t1 bt t2.t_ty

exception EmptyCase

let t_case t bl =
  let tty = t_type t in
  let bty = match bl with
    | (_,_,tbr) :: _ -> tbr.t_ty
    | _ -> raise EmptyCase
  in
  let t_check_branch (p,_,tbr) =
    ty_equal_check tty p.pat_ty;
    t_ty_check tbr bty
  in
  List.iter t_check_branch bl;
  t_case t bl bty

let t_eps ((v,_,f) as bf) =
  ignore (t_prop f);
  t_eps bf (Some v.vs_ty)

let t_quant q ((vl,_,_,f) as qf) =
  if vl = [] then f else t_quant q qf

let t_binary op f1 f2 = t_binary op (t_prop f1) (t_prop f2)
let t_not f = t_not (t_prop f)

let t_forall  = t_quant Tforall
let t_exists  = t_quant Texists
let t_and     = t_binary Tand
let t_or      = t_binary Tor
let t_implies = t_binary Timplies
let t_iff     = t_binary Tiff

let rec t_and_l = function
  | [] -> t_true
  | [f] -> f
  | f::fl -> t_and f (t_and_l fl)

let rec t_or_l = function
  | [] -> t_false
  | [f] -> f
  | f::fl -> t_or f (t_or_l fl)

let asym_split = create_attribute "asym_split"
let stop_split = create_attribute "stop_split"

let t_and_asym t1 t2 = t_and (t_attr_add asym_split t1) t2
let t_or_asym  t1 t2 = t_or  (t_attr_add asym_split t1) t2

let rec t_and_asym_l = function
  | [] -> t_true
  | [f] -> f
  | f::fl -> t_and_asym f (t_and_asym_l fl)

let rec t_or_asym_l = function
  | [] -> t_false
  | [f] -> f
  | f::fl -> t_or_asym f (t_or_asym_l fl)

(* closing constructors *)

let t_quant_close q vl tl f =
  if vl = [] then t_prop f else t_quant q (t_close_quant vl tl f)

let t_forall_close = t_quant_close Tforall
let t_exists_close = t_quant_close Texists

let t_let_close v t1 t2 = t_let t1 (t_close_bound v t2)
let t_case_close t l = t_case t (List.map (fun (p,e) -> t_close_branch p e) l)
let t_eps_close v f = t_eps (t_close_bound v f)

(* built-in symbols *)

let ps_equ =
  let v = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh (op_infix "=")) [v; v]

let t_equ t1 t2 = ps_app ps_equ [t1; t2]
let t_neq t1 t2 = t_not (ps_app ps_equ [t1; t2])

let fs_bool_true  = create_fsymbol ~constr:2 (id_fresh "True")  [] ty_bool
let fs_bool_false = create_fsymbol ~constr:2 (id_fresh "False") [] ty_bool

let t_bool_true  = fs_app fs_bool_true [] ty_bool
let t_bool_false = fs_app fs_bool_false [] ty_bool

let fs_tuple_ids = Hid.create 17

let fs_tuple = Hint.memo 17 (fun n ->
  let ts = ts_tuple n in
  let tl = List.map ty_var ts.ts_args in
  let ty = ty_app ts tl in
  let id = id_fresh ("Tuple" ^ string_of_int n) in
  let fs = create_fsymbol ~constr:1 id tl ty in
  Hid.add fs_tuple_ids fs.ls_name n;
  fs)

let is_fs_tuple fs =
  fs.ls_constr = 1 && Hid.mem fs_tuple_ids fs.ls_name

let is_fs_tuple_id id =
  try Some (Hid.find fs_tuple_ids id) with Not_found -> None

let t_tuple tl =
  let ty = ty_tuple (List.map t_type tl) in
  fs_app (fs_tuple (List.length tl)) tl ty

let fs_func_app =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  let ty_b = ty_var (create_tvsymbol (id_fresh "b")) in
  let id = id_fresh (op_infix "@") in
  create_fsymbol id [ty_func ty_a ty_b; ty_a] ty_b

let t_func_app fn t = t_app_infer fs_func_app [fn; t]
let t_pred_app pr t = t_equ (t_func_app pr t) t_bool_true

let t_func_app_l fn tl = List.fold_left t_func_app fn tl
let t_pred_app_l pr tl = t_equ (t_func_app_l pr tl) t_bool_true

(** Term library *)

(* generic map over types, symbols and variables *)

let gen_fresh_vsymbol fnT v =
  let ty = fnT v.vs_ty in
  if ty_equal ty v.vs_ty then v else
  create_vsymbol (id_clone v.vs_name) ty

let gen_vs_rename fnT h v =
  let u = gen_fresh_vsymbol fnT v in
  Mvs.add v u h, u

let gen_vl_rename fnT h vl =
  Lists.map_fold_left (gen_vs_rename fnT) h vl

let gen_pat_rename fnT fnL h p =
  let add_vs v () = gen_fresh_vsymbol fnT v in
  let m = Mvs.mapi add_vs p.pat_vars in
  let p = pat_gen_map fnT fnL m p in
  Mvs.union (fun _ _ t -> Some t) h m, p

let gen_bnd_rename fnT fnE h b =
  let add_bv v n m = Mvs.add (Mvs.find v h) n m in
  let bvs = Mvs.fold add_bv b.bv_vars Mvs.empty in
  let add_bs v t (nh, m) =
    let nh,v = gen_vs_rename fnT nh v in
    nh, Mvs.add v (fnE t) m
  in
  let h,bsb = Mvs.fold add_bs b.bv_subst (h,Mvs.empty) in
  h, { bv_vars = bvs ; bv_subst = bsb }

let rec t_gen_map fnT fnL m t =
  let fn = t_gen_map fnT fnL m in
  t_attr_copy t (match t.t_node with
    | Tvar v ->
        let u = Mvs.find_def v v m in
        ty_equal_check (fnT v.vs_ty) u.vs_ty;
        t_var u
    | Tconst _ ->
        t
    | Tapp (fs, tl) ->
        t_app (fnL fs) (List.map fn tl) (Opt.map fnT t.t_ty)
    | Tif (f, t1, t2) ->
        t_if (fn f) (fn t1) (fn t2)
    | Tlet (t1, (u,b,t2)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_let (fn t1) (u, b, t_gen_map fnT fnL m t2)
    | Tcase (t1, bl) ->
        let fn_br (p,b,t2) =
          let m,b = gen_bnd_rename fnT fn m b in
          let m,p = gen_pat_rename fnT fnL m p in
          (p, b, t_gen_map fnT fnL m t2)
        in
        t_case (fn t1) (List.map fn_br bl)
    | Teps (u,b,f) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,u = gen_vs_rename fnT m u in
        t_eps (u, b, t_gen_map fnT fnL m f)
    | Tquant (q, (vl,b,tl,f)) ->
        let m,b = gen_bnd_rename fnT fn m b in
        let m,vl = gen_vl_rename fnT m vl in
        let fn = t_gen_map fnT fnL m in
        t_quant q (vl, b, tr_map fn tl, fn f)
    | Tbinop (op, f1, f2) ->
        t_binary op (fn f1) (fn f2)
    | Tnot f1 ->
        t_not (fn f1)
    | Ttrue | Tfalse ->
        t)

let t_gen_map fnT fnL mapV t = t_gen_map (Wty.memoize 17 fnT) fnL mapV t

(* map over type and logic symbols *)

let gen_mapV fnT = Mvs.mapi (fun v _ -> gen_fresh_vsymbol fnT v)

let t_s_map fnT fnL t = t_gen_map fnT fnL (gen_mapV fnT (t_vars t)) t

(* simultaneous substitution into types and terms *)

let t_subst_types mapT mapV t =
  let fnT = ty_inst mapT in
  let m = gen_mapV fnT (t_vars t) in
  let t = t_gen_map fnT (fun ls -> ls) m t in
  let add _ v t m = vs_check v t; Mvs.add v t m in
  let m = Mvs.fold2_inter add m mapV Mvs.empty in
  (m,t)

let t_ty_subst mapT mapV t =
  let m,t = t_subst_types mapT mapV t in
  t_subst_unsafe m t

(* fold over symbols *)

let rec t_gen_fold fnT fnL acc t =
  let fn = t_gen_fold fnT fnL in
  let acc = Opt.fold fnT acc t.t_ty in
  match t.t_node with
  | Tconst _ | Tvar _ -> acc
  | Tapp (f, tl) -> List.fold_left fn (fnL acc f) tl
  | Tif (f, t1, t2) -> fn (fn (fn acc f) t1) t2
  | Tlet (t1, (_,b,t2)) -> fn (bnd_fold fn (fn acc t1) b) t2
  | Tcase (t1, bl) ->
      let branch acc (p,b,t) =
        fn (pat_gen_fold fnT fnL (bnd_fold fn acc b) p) t in
      List.fold_left branch (fn acc t1) bl
  | Teps (_,b,f) -> fn (bnd_fold fn acc b) f
  | Tquant (_, (vl,b,tl,f1)) ->
      (* these variables (and their types) may never appear below *)
      let acc = List.fold_left (fun a v -> fnT a v.vs_ty) acc vl in
      fn (tr_fold fn (bnd_fold fn acc b) tl) f1
  | Tbinop (_, f1, f2) -> fn (fn acc f1) f2
  | Tnot f1 -> fn acc f1
  | Ttrue | Tfalse -> acc

let t_s_fold = t_gen_fold

let t_s_all prT prL t = Util.alld t_s_fold prT prL t
let t_s_any prT prL t = Util.anyd t_s_fold prT prL t

(* map/fold over types in terms and formulas *)

let t_ty_map fn t = t_s_map fn (fun ls -> ls) t

let t_ty_fold fn acc t = t_s_fold fn Util.const acc t

let t_ty_freevars = t_ty_fold ty_freevars

(* map/fold over applications in terms and formulas (but not in patterns!) *)

let rec t_app_map fn t =
  let t = t_map_unsafe (t_app_map fn) t in
  match t.t_node with
    | Tapp (ls,tl) ->
        let ls = fn ls (List.map t_type tl) t.t_ty in
        t_attr_copy t (t_app ls tl t.t_ty)
    | _ -> t

let rec t_app_fold fn acc t =
  let acc = t_fold_unsafe (t_app_fold fn) acc t in
  match t.t_node with
    | Tapp (ls,tl) -> fn acc ls (List.map t_type tl) t.t_ty
    | _ -> acc

(* Type- and binding-safe traversal *)

let t_map fn t = match t.t_node with
  | Tlet (t1, b) ->
      let u,t2 = t_open_bound b in
      let s1 = fn t1 and s2 = fn t2 in
      if s2 == t2
        then if s1 == t1 then t
          else t_attr_copy t (t_let s1 b)
        else t_attr_copy t (t_let_close u s1 s2)
  | Tcase (t1, bl) ->
      let s1 = fn t1 in
      let brn same b =
        let p,t = t_open_branch b in
        let s = fn t in
        if s == t then same, b
          else false, t_close_branch p s
      in
      let same, bl = Lists.map_fold_left brn true bl in
      if s1 == t1 && same then t
        else t_attr_copy t (t_case s1 bl)
  | Teps b ->
      let u,t1 = t_open_bound b in
      let s1 = fn t1 in
      if s1 == t1 then t
        else t_attr_copy t (t_eps_close u s1)
  | Tquant (q, b) ->
      let vl,tl,f1 = t_open_quant b in
      let g1 = fn f1 and sl = tr_map fn tl in
      if g1 == f1 && List.for_all2 (List.for_all2 (==)) sl tl then t
        else t_attr_copy t (t_quant_close q vl sl g1)
  | _ ->
      t_map_unsafe fn t

let t_map fn = t_map (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)

(* safe opening fold *)

let t_fold fn acc t = match t.t_node with
  | Tlet (t1, b) ->
      let _,t2 = t_open_bound b in fn (fn acc t1) t2
  | Tcase (t1, bl) ->
      let brn acc b = let _,t = t_open_branch b in fn acc t in
      List.fold_left brn (fn acc t1) bl
  | Teps b ->
      let _,f = t_open_bound b in fn acc f
  | Tquant (_, b) ->
      let _, tl, f1 = t_open_quant b in tr_fold fn (fn acc f1) tl
  | _ -> t_fold_unsafe fn acc t

let t_iter fn t = t_fold (fun () t -> fn t) () t

let t_all pr t = Util.all t_fold pr t
let t_any pr t = Util.any t_fold pr t

(* safe opening map_fold *)

let t_map_fold fn acc t = match t.t_node with
  | Tlet (t1, b) ->
      let acc, s1 = fn acc t1 in
      let u,t2 = t_open_bound b in
      let acc, s2 = fn acc t2 in
      acc, if s2 == t2
        then if s1 == t1 then t
          else t_attr_copy t (t_let s1 b)
        else t_attr_copy t (t_let_close u s1 s2)
  | Tcase (t1, bl) ->
      let acc, s1 = fn acc t1 in
      let brn (acc,same) b =
        let p,t = t_open_branch b in
        let acc, s = fn acc t in
        if s == t then (acc,same), b
          else (acc,false), t_close_branch p s
      in
      let (acc,same), bl = Lists.map_fold_left brn (acc,true) bl in
      acc, if s1 == t1 && same then t
        else t_attr_copy t (t_case s1 bl)
  | Teps b ->
      let u,t1 = t_open_bound b in
      let acc, s1 = fn acc t1 in
      acc, if s1 == t1 then t
        else t_attr_copy t (t_eps_close u s1)
  | Tquant (q, b) ->
      let vl,tl,f1 = t_open_quant b in
      let acc, sl = tr_map_fold fn acc tl in
      let acc, g1 = fn acc f1 in
      acc, if g1 == f1 && List.for_all2 (List.for_all2 (==)) sl tl
        then t else t_attr_copy t (t_quant_close q vl sl g1)
  | _ -> t_map_fold_unsafe fn acc t

let t_map_fold fn = t_map_fold (fun acc t ->
  let res = fn acc t in t_ty_check (snd res) t.t_ty; res)

(* polarity map *)

let t_map_sign fn sign f = t_attr_copy f (match f.t_node with
  | Tbinop (Timplies, f1, f2) ->
      t_implies (fn (not sign) f1) (fn sign f2)
  | Tbinop (Tiff, f1, f2) ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2p = fn sign f2 in let f2n = fn (not sign) f2 in
      if t_equal f1p f1n && t_equal f2p f2n then t_iff f1p f2p
      else if sign
        then t_and (t_implies f1n f2p) (t_implies f2n f1p)
        else t_implies (t_or f1n f2n) (t_and f1p f2p)
  | Tnot f1 ->
      t_not (fn (not sign) f1)
  | Tif (f1, f2, f3) when f.t_ty = None ->
      let f1p = fn sign f1 in let f1n = fn (not sign) f1 in
      let f2 = fn sign f2 in let f3 = fn sign f3 in
      if t_equal f1p f1n then t_if f1p f2 f3 else if sign
        then t_and (t_implies f1n f2) (t_implies (t_not f1p) f3)
        else t_or (t_and f1p f2) (t_and (t_not f1n) f3)
  | Tif _
  | Teps _ -> failwith "t_map_sign: cannot determine polarity"
  | _ -> t_map (fn sign) f)

(* continuation-passing traversal *)

let rec list_map_cont fnL contL = function
  | e::el ->
      let cont_l e el = contL (e::el) in
      let cont_e e = list_map_cont fnL (cont_l e) el in
      fnL cont_e e
  | [] ->
      contL []

let t_map_cont fn contT t =
  let contT e = contT (t_attr_copy t e) in
  match t.t_node with
  | Tvar _ | Tconst _ -> contT t
  | Tapp (fs, tl) ->
      let cont_app tl = contT (t_app fs tl t.t_ty) in
      list_map_cont fn cont_app tl
  | Tif (f, t1, t2) ->
      let cont_else f t1 t2 = contT (t_if f t1 t2) in
      let cont_then f t1 = fn (cont_else f t1) t2 in
      let cont_if f = fn (cont_then f) t1 in
      fn cont_if f
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let cont_in t1 t2 = contT (t_let t1 (close u t2)) in
      let cont_let t1 = fn (cont_in t1) t2 in
      fn cont_let t1
  | Tcase (t1, bl) ->
      let fnB contB b =
        let pat,t,close = t_open_branch_cb b in
        fn (fun t -> contB (close pat t)) t
      in
      let cont_with t1 bl = contT (t_case t1 bl) in
      let cont_case t1 = list_map_cont fnB (cont_with t1) bl in
      fn cont_case t1
  | Teps b ->
      let u,f,close = t_open_bound_cb b in
      let cont_eps f = contT (t_eps (close u f)) in
      fn cont_eps f
  | Tquant (q, b) ->
      let vl, tl, f1, close = t_open_quant_cb b in
      let cont_dot tl f1 = contT (t_quant q (close vl tl f1)) in
      let cont_quant tl = fn (cont_dot tl) f1 in
      list_map_cont (list_map_cont fn) cont_quant tl
  | Tbinop (op, f1, f2) ->
      let cont_r f1 f2 = contT (t_binary op f1 f2) in
      let cont_l f1 = fn (cont_r f1) f2 in
      fn cont_l f1
  | Tnot f1 ->
      let cont_not f1 = contT (t_not f1) in
      fn cont_not f1
  | Ttrue | Tfalse -> contT t

let t_map_cont fn = t_map_cont (fun cont t ->
  fn (fun e -> t_ty_check e t.t_ty; cont e) t)

(* map/fold over free variables *)

let t_v_map fn t =
  let fn v _ = let res = fn v in vs_check v res; res in
  t_subst_unsafe (Mvs.mapi fn (t_vars t)) t

let bnd_v_fold fn acc b = Mvs.fold (fun v _ acc -> fn acc v) b.bv_vars acc

let bound_v_fold fn acc (_,b,_) = bnd_v_fold fn acc b

let rec t_v_fold fn acc t = match t.t_node with
  | Tvar v -> fn acc v
  | Tlet (e,b) -> bound_v_fold fn (t_v_fold fn acc e) b
  | Tcase (e,bl) -> List.fold_left (bound_v_fold fn) (t_v_fold fn acc e) bl
  | Teps b -> bound_v_fold fn acc b
  | Tquant (_,(_,b,_,_)) -> bnd_v_fold fn acc b
  | _ -> t_fold_unsafe (t_v_fold fn) acc t

let t_v_all pr t = Util.all t_v_fold pr t
let t_v_any pr t = Util.any t_v_fold pr t

let t_closed t = t_v_all Util.ffalse t

let bnd_v_count fn acc b = Mvs.fold (fun v n acc -> fn acc v n) b.bv_vars acc

let bound_v_count fn acc (_,b,_) = bnd_v_count fn acc b

let rec t_v_count fn acc t = match t.t_node with
  | Tvar v -> fn acc v 1
  | Tlet (e,b) -> bound_v_count fn (t_v_count fn acc e) b
  | Tcase (e,bl) -> List.fold_left (bound_v_count fn) (t_v_count fn acc e) bl
  | Teps b -> bound_v_count fn acc b
  | Tquant (_,(_,b,_,_)) -> bnd_v_count fn acc b
  | _ -> t_fold_unsafe (t_v_count fn) acc t

let t_v_occurs v t =
  t_v_count (fun c u n -> if vs_equal u v then c + n else c) 0 t

(* replaces variables with terms in term [t] using map [m] *)

let t_subst m t = Mvs.iter vs_check m; t_subst_unsafe m t

let t_subst_single v t1 t = t_subst (Mvs.singleton v t1) t

(* set of free variables *)

let t_freevars = add_t_vars

(* occurrence check *)

let rec t_occurs r t =
  t_equal r t || t_any (t_occurs r) t

(* substitutes term [t2] for term [t1] in term [t] *)

let rec t_replace t1 t2 t =
  if t_equal t t1 then t2 else t_map (t_replace t1 t2) t

let t_replace t1 t2 t =
  t_ty_check t2 t1.t_ty;
  t_replace t1 t2 t

(* lambdas *)

let t_lambda vl trl t =
  let ty = Opt.get_def ty_bool t.t_ty in
  let add_ty v ty = ty_func v.vs_ty ty in
  let ty = List.fold_right add_ty vl ty in
  let fc = create_vsymbol (id_fresh "fc") ty in
  let copy_loc e = if t.t_loc = None then e
    else t_attr_set ?loc:t.t_loc e.t_attrs e in
  let mk_t_var v = if v.vs_name.id_loc = None then t_var v
    else t_attr_set ?loc:v.vs_name.id_loc Sattr.empty (t_var v) in
  let add_arg h v = copy_loc (t_func_app h (mk_t_var v)) in
  let h = List.fold_left add_arg (mk_t_var fc) vl in
  let f = match t.t_ty with
    | Some _ -> t_equ h t
    | None   -> t_iff (copy_loc (t_equ h t_bool_true)) t in
  t_eps_close fc (copy_loc (t_forall_close vl trl (copy_loc f)))

let t_lambda vl trl t =
  let t = match t.t_node with
    | Tapp (ps,[l;{t_node = Tapp (fs,[])}])
      when ls_equal ps ps_equ && ls_equal fs fs_bool_true ->
        t_attr_copy t l
    | _ -> t in
  if vl <> [] then t_lambda vl trl t
  else if t.t_ty <> None then t
  else t_if t t_bool_true t_bool_false

let t_open_lambda t = match t.t_ty, t.t_node with
  | Some {ty_node = Tyapp (ts,_)}, Teps fb when ts_equal ts ts_func ->
      let fc,f = t_open_bound fb in
      let vl,trl,f = match f.t_node with
        | Tquant (Tforall,fq) -> t_open_quant fq
        | _ -> [], [], t (* fail the next check *) in
      let h,e = match f.t_node with
        | Tapp (ps,[h;e]) when ls_equal ps ps_equ -> h, e
        | Tbinop (Tiff,{t_node = Tapp (ps,[h;{t_node = Tapp (fs,[])}])},e)
          when ls_equal ps ps_equ && ls_equal fs fs_bool_true -> h, e
        | _ -> t, t (* fail the next check *) in
      let rec check h xl = match h.t_node, xl with
        | Tapp (fs,[h;{t_node = Tvar u}]), x::xl
          when ls_equal fs fs_func_app && vs_equal u x -> check h xl
        | Tvar u, [] when vs_equal u fc && t_v_occurs u e = 0 -> vl, trl, e
        | _ -> [], [], t in
      check h (List.rev vl)
  | _ -> [], [], t

(* it is rather tricky to check if a term is a lambda without properly
   opening the binders. The deferred substitution in the quantifier
   may obscure the closure variable or, on the contrary, introduce it
   on the RHS of the definition, making it recursive. We cannot simply
   reject such deferred substitutions, because the closure variable is
   allowed in the triggers and it can appear there via the deferred
   substitution, why not? Therefore, t_is_lambda is a mere shim around
   t_open_lambda. *)
let t_is_lambda t = let vl,_,_ = t_open_lambda t in vl <> []

let t_open_lambda_cb t =
  let vl, trl, e = t_open_lambda t in
  let close vl' trl' e' =
    if e == e' &&
      Lists.equal (Lists.equal ((==) : term -> term -> bool)) trl trl' &&
      Lists.equal vs_equal vl vl'
    then t else t_lambda vl' trl' e' in
  vl, trl, e, close

let t_closure ls tyl ty =
  let mk_v i ty = create_vsymbol (id_fresh ("y" ^ string_of_int i)) ty in
  let vl = Lists.mapi mk_v tyl in
  let t = t_app ls (List.map t_var vl) ty in
  t_lambda vl [] t

let t_app_partial ls tl tyl ty =
  if tyl = [] then t_app ls tl ty else
  match tl with
  | [t] when ls_equal ls fs_func_app -> t
  | _ ->
      let cons t tyl = t_type t :: tyl in
      let tyl = List.fold_right cons tl tyl in
      t_func_app_l (t_closure ls tyl ty) tl

let rec t_app_beta_l lam tl =
  if tl = [] then lam else
  let vl, trl, e = t_open_lambda lam in
  if vl = [] then t_func_app_l lam tl else
  let rec add m vl tl = match vl, tl with
    | [], tl ->
        t_app_beta_l (t_subst_unsafe m e) tl
    | vl, [] ->
        let trl = List.map (List.map (t_subst_unsafe m)) trl in
        t_lambda vl trl (t_subst_unsafe m e)
    | v::vl, t::tl ->
        vs_check v t; add (Mvs.add v t m) vl tl in
  add Mvs.empty vl tl

let t_func_app_beta_l lam tl =
  let e = t_app_beta_l lam tl in
  if e.t_ty = None then t_if e t_bool_true t_bool_false else e

let t_pred_app_beta_l lam tl =
  let e = t_app_beta_l lam tl in
  if e.t_ty = None then e else t_equ e t_bool_true

let t_func_app_beta lam t = t_func_app_beta_l lam [t]
let t_pred_app_beta lam t = t_pred_app_beta_l lam [t]

(* constructors with propositional simplification *)

let t_not_simp f = match f.t_node with
  | Ttrue  -> t_attr_copy f t_false
  | Tfalse -> t_attr_copy f t_true
  | Tnot g -> t_attr_copy f g
  | _      -> t_not f

let t_and_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> t_attr_remove asym_split f1
  | Tfalse, _ -> t_attr_remove asym_split f1
  | _, Tfalse -> f2
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_and f1 f2

let t_and_simp_l l = List.fold_right t_and_simp l t_true

let t_or_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> t_attr_remove asym_split f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> t_attr_remove asym_split f1
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_or f1 f2

let t_or_simp_l l = List.fold_right t_or_simp l t_false

let t_and_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> t_attr_remove asym_split f1
  | Tfalse, _ -> t_attr_remove asym_split f1
  | _, Tfalse -> f2
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_and_asym f1 f2

let t_and_asym_simp_l l = List.fold_right t_and_asym_simp l t_true

let t_or_asym_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> t_attr_remove asym_split f1
  | _, Ttrue  -> f2
  | Tfalse, _ -> f2
  | _, Tfalse -> t_attr_remove asym_split f1
  | _, _ when t_equal f1 f2 -> f1
  | _, _ -> t_or_asym f1 f2

let t_or_asym_simp_l l = List.fold_right t_or_asym_simp l t_false

let t_implies_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f2
  | Tfalse, _ -> t_attr_copy f1 t_true
  | _, Tfalse -> t_not_simp f1
  | _, _ when t_equal f1 f2 -> t_attr_copy f1 t_true
  | _, _ -> t_implies f1 f2

let t_iff_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  -> f2
  | _, Ttrue  -> f1
  | Tfalse, _ -> t_not_simp f2
  | _, Tfalse -> t_not_simp f1
  | _, _ when t_equal f1 f2 -> t_attr_copy f1 t_true
  | _, _ -> t_iff f1 f2

let t_binary_simp op = match op with
  | Tand     -> t_and_simp
  | Tor      -> t_or_simp
  | Timplies -> t_implies_simp
  | Tiff     -> t_iff_simp

let t_if_simp f1 f2 f3 = match f1.t_node, f2.t_node, f3.t_node with
  | Ttrue, _, _  -> f2
  | Tfalse, _, _ -> f3
  | _, Ttrue, _  -> t_implies_simp (t_not_simp f1) f3
  | _, Tfalse, _ -> t_and_asym_simp (t_not_simp f1) f3
  | _, _, Ttrue  -> t_implies_simp f1 f2
  | _, _, Tfalse -> t_and_asym_simp f1 f2
  | _, _, _ when t_equal f2 f3 -> f2
  | _, _, _ -> t_if f1 f2 f3

let small t = match t.t_node with
  | Tvar _ | Tconst _ -> true
(* NOTE: shouldn't we allow this?
  | Tapp (_,[]) -> true
*)
  | _ -> false

let t_let_simp e ((v,b,t) as bt) =
  let n = t_v_occurs v t in
  if n = 0 then
    t_subst_unsafe b.bv_subst t else
  if n = 1 || small e then begin
    vs_check v e;
    t_subst_unsafe (Mvs.add v e b.bv_subst) t
  end else
    t_let e bt

let t_let_close_simp v e t =
  let n = t_v_occurs v t in
  if n = 0 then t else
  if n = 1 || small e then
    t_subst_single v e t
  else
    t_let_close v e t

let t_case_simp t bl =
  let e0,tl = match bl with
    | [] -> raise EmptyCase
    | (_,_,e0)::tl -> e0,tl in
  let e0_true = match e0.t_node with
    | Ttrue -> true | _ -> false in
  let e0_false = match e0.t_node with
    | Tfalse -> true | _ -> false in
  let is_e0 (_,_,e) = match e.t_node with
    | Ttrue -> e0_true
    | Tfalse -> e0_false
    | _ -> t_equal e e0 in
  if t_closed e0 && List.for_all is_e0 tl then e0
  else t_case t bl

let t_case_close_simp t bl =
  let e0,tl = match bl with
    | [] -> raise EmptyCase
    | (_,e0)::tl -> e0,tl in
  let e0_true = match e0.t_node with
    | Ttrue -> true | _ -> false in
  let e0_false = match e0.t_node with
    | Tfalse -> true | _ -> false in
  let is_e0 (_,e) = match e.t_node with
    | Ttrue -> e0_true
    | Tfalse -> e0_false
    | _ -> t_equal e e0 in
  if t_closed e0 && List.for_all is_e0 tl then e0
  else t_case_close t bl

let t_quant_simp q ((vl,_,_,f) as qf) =
  let fvs = t_vars f in
  let check v = Mvs.mem v fvs in
  if List.for_all check vl then
    t_quant q qf
  else
    let vl,tl,f = t_open_quant qf in
    let fvs = t_vars f in
    let check v = Mvs.mem v fvs in
    let vl = List.filter check vl in
    if vl = [] then f
    else t_quant_close q vl (List.filter (List.for_all (t_v_all check)) tl) f

let t_quant_close_simp q vl tl f =
  if vl = [] then f else
  let fvs = t_vars f in
  let check v = Mvs.mem v fvs in
  if List.for_all check vl then
    t_quant_close q vl tl f
  else
    let vl = List.filter check vl in
    if vl = [] then f
    else t_quant_close q vl (List.filter (List.for_all (t_v_all check)) tl) f

let t_forall_simp = t_quant_simp Tforall
let t_exists_simp = t_quant_simp Texists

let t_forall_close_simp = t_quant_close_simp Tforall
let t_exists_close_simp = t_quant_close_simp Texists

let t_equ_simp t1 t2 =
  if t_equal t1 t2 then t_true  else t_equ t1 t2

let t_neq_simp t1 t2 =
  if t_equal t1 t2 then t_false else t_neq t1 t2

let t_forall_close_merge vs f = match f.t_node with
  | Tquant (Tforall, fq) ->
      let vs', trs, f = t_open_quant fq in
      t_forall_close (vs@vs') trs f
  | _ -> t_forall_close vs [] f

let t_exists_close_merge vs f = match f.t_node with
  | Tquant (Texists, fq) ->
      let vs', trs, f = t_open_quant fq in
      t_exists_close (vs@vs') trs f
  | _ -> t_exists_close vs [] f

let t_map_simp fn f = t_attr_copy f (match f.t_node with
  | Tapp (p, [t1;t2]) when ls_equal p ps_equ ->
      t_equ_simp (fn t1) (fn t2)
  | Tif (f1, f2, f3) ->
      t_if_simp (fn f1) (fn f2) (fn f3)
  | Tlet (t, b) ->
      let u,t2,close = t_open_bound_cb b in
      t_let_simp (fn t) (close u (fn t2))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      t_quant_simp q (close vl (tr_map fn tl) (fn f1))
  | Tbinop (op, f1, f2) ->
      t_binary_simp op (fn f1) (fn f2)
  | Tnot f1 ->
      t_not_simp (fn f1)
  | _ -> t_map fn f)

let t_map_simp fn = t_map_simp (fun t ->
  let res = fn t in t_ty_check res t.t_ty; res)

(** Traversal with separate functions for value-typed and prop-typed terms *)

module TermTF = struct
  let t_select fnT fnF e =
    if e.t_ty = None then fnF e else fnT e

  let t_selecti fnT fnF acc e =
    if e.t_ty = None then fnF acc e else fnT acc e

  let t_map fnT fnF = t_map (t_select fnT fnF)
  let t_fold fnT fnF = t_fold (t_selecti fnT fnF)
  let t_map_fold fnT fnF = t_map_fold (t_selecti fnT fnF)
  let t_all prT prF = t_all (t_select prT prF)
  let t_any prT prF = t_any (t_select prT prF)
  let t_map_simp fnT fnF = t_map_simp (t_select fnT fnF)
  let t_map_sign fnT fnF = t_map_sign (t_selecti fnT fnF)
  let t_map_cont fnT fnF = t_map_cont (t_selecti fnT fnF)
  let tr_map fnT fnF = tr_map (t_select fnT fnF)
  let tr_fold fnT fnF = tr_fold (t_selecti fnT fnF)
  let tr_map_fold fnT fnF = tr_map_fold (t_selecti fnT fnF)
end
