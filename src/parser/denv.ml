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

open Format
open Pp
open Util
open Ptree
open Ident
open Ty
open Term
open Theory

type error = 
  | AnyMessage of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let report fmt = function
  | AnyMessage s ->
      fprintf fmt "%s" s

let () = Exn_printer.register
  (fun fmt exn -> match exn with
    | Error error -> report fmt error
    | _ -> raise exn)

(** types with destructive type variables *)

type dty =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list
      
and type_var = { 
  tag : int; 
  user : bool;
  tvsymbol : tvsymbol;
  mutable type_val : dty option;
  type_var_loc : loc option;
}

let rec print_dty fmt = function
  | Tyvar { type_val = Some t } ->
      print_dty fmt t
  | Tyvar { type_val = None; tvsymbol = v } ->
      fprintf fmt "'%s" v.tv_name.id_string
  | Tyapp (s, []) ->
      fprintf fmt "%s" s.ts_name.id_string
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %s" print_dty t s.ts_name.id_string
  | Tyapp (s, l) -> 
      fprintf fmt "(%a) %s" 
	(print_list comma print_dty) l s.ts_name.id_string

let create_ty_decl_var =
  let t = ref 0 in
  fun ?loc ~user tv -> 
    incr t; 
    { tag = !t; user = user; tvsymbol = tv; type_val = None;
      type_var_loc = loc }

let rec occurs v = function
  | Tyvar { type_val = Some t } -> occurs v t
  | Tyvar { tag = t; type_val = None } -> v.tag = t
  | Tyapp (_, l) -> List.exists (occurs v) l

(* destructive type unification *)
let rec unify t1 t2 = match t1, t2 with
  | Tyvar { type_val = Some t1 }, _ ->
      unify t1 t2
  | _, Tyvar { type_val = Some t2 } ->
      unify t1 t2
  | Tyvar v1, Tyvar v2 when v1.tag = v2.tag ->
      true
	(* instantiable variables *)
  | Tyvar ({user=false} as v), t
  | t, Tyvar ({user=false} as v) ->
      not (occurs v t) && (v.type_val <- Some t; true)
	(* recursive types *)
  | Tyapp (s1, l1), Tyapp (s2, l2) ->
      ts_equal s1 s2 && List.length l1 = List.length l2 &&
	  List.for_all2 unify l1 l2
  | Tyapp _, _ | _, Tyapp _ ->
      false
	(* other cases *)
  | Tyvar {user=true; tag=t1}, Tyvar {user=true; tag=t2} -> 
      t1 = t2

(* intermediate types -> types *)
let rec ty_of_dty = function
  | Tyvar { type_val = Some t } ->
      ty_of_dty t
  | Tyvar { type_val = None; user = false; type_var_loc = loc } ->
      error ?loc (AnyMessage "undefined type variable")
  | Tyvar { tvsymbol = tv } ->
      ty_var tv
  | Tyapp (s, tl) ->
      ty_app s (List.map ty_of_dty tl)

type dpattern = { dp_node : dpattern_node; dp_ty : dty }

and dpattern_node =
  | Pwild
  | Pvar of string
  | Papp of lsymbol * dpattern list
  | Pas of dpattern * string

let rec pattern env p =
  let ty = ty_of_dty p.dp_ty in
  match p.dp_node with
  | Pwild -> 
      env, pat_wild ty
  | Pvar x ->
      let v = create_vsymbol (id_fresh x) ty in
      Mstr.add x v env, pat_var v
  | Papp (s, pl) ->
      let env, pl = map_fold_left pattern env pl in
      env, pat_app s pl ty
  | Pas (p, x) ->
      let v = create_vsymbol (id_fresh x) ty in
      let env, p = pattern (Mstr.add x v env) p in
      env, pat_as p v

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tvar of string
  | Tconst of constant
  | Tapp of lsymbol * dterm list
  | Tif of dfmla * dterm * dterm
  | Tlet of dterm * string * dterm
  | Tmatch of dterm list * (dpattern list * dterm) list
  | Tnamed of string * dterm
  | Teps of string * dty * dfmla

and dfmla =
  | Fapp of lsymbol * dterm list
  | Fquant of quant * (string * dty) list * dtrigger list list * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
  | Flet of dterm * string * dfmla
  | Fmatch of dterm list * (dpattern list * dfmla) list
  | Fnamed of string * dfmla
  | Fvar of fmla

and dtrigger =
  | TRterm of dterm
  | TRfmla of dfmla

let rec term env t = match t.dt_node with
  | Tvar x ->
      assert (Mstr.mem x env);
      t_var (Mstr.find x env)
  | Tconst c ->
      t_const c (ty_of_dty t.dt_ty)
  | Tapp (s, tl) ->
      t_app s (List.map (term env) tl) (ty_of_dty t.dt_ty)
  | Tif (f, t1, t2) ->
      t_if (fmla env f) (term env t1) (term env t2)
  | Tlet (e1, x, e2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let e2 = term env e2 in
      t_let v e1 e2
  | Tmatch (tl, bl) ->
      let branch (pl,e) =
        let env, pl = map_fold_left pattern env pl in
        (pl, term env e)
      in
      let bl = List.map branch bl in
      let ty = (snd (List.hd bl)).t_ty in
      t_case (List.map (term env) tl) bl ty
  | Tnamed (x, e1) ->
      let e1 = term env e1 in
      t_label_add x e1
  | Teps (x, ty, e1) ->
      let ty = ty_of_dty ty in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let e1 = fmla env e1 in
      t_eps v e1

and fmla env = function
  | Ftrue ->
      f_true
  | Ffalse ->
      f_false
  | Fnot f ->
      f_not (fmla env f)
  | Fbinop (op, f1, f2) ->
      f_binary op (fmla env f1) (fmla env f2)
  | Fif (f1, f2, f3) ->
      f_if (fmla env f1) (fmla env f2) (fmla env f3)
  | Fquant (q, uqu, trl, f1) ->
      (* TODO: shouldn't we localize this ident? *)
      let uquant env (x,ty) =
        let ty = ty_of_dty ty in
        let v = create_vsymbol (id_fresh x) ty in
        Mstr.add x v env, v
      in
      let env, vl = map_fold_left uquant env uqu in
      let trigger = function
	| TRterm t -> Term (term env t)
	| TRfmla f -> Fmla (fmla env f)
      in
      let trl = List.map (List.map trigger) trl in
      f_quant q vl trl (fmla env f1)
  | Fapp (s, tl) ->
      f_app s (List.map (term env) tl)
  | Flet (e1, x, f2) ->
      let ty = ty_of_dty e1.dt_ty in
      let e1 = term env e1 in
      let v = create_vsymbol (id_fresh x) ty in
      let env = Mstr.add x v env in
      let f2 = fmla env f2 in
      f_let v e1 f2
  | Fmatch (tl, bl) ->
      let branch (pl,e) =
        let env, pl = map_fold_left pattern env pl in
        (pl, fmla env e)
      in
      f_case (List.map (term env) tl) (List.map branch bl)
  | Fnamed (x, f1) ->
      let f1 = fmla env f1 in
      f_label_add x f1
  | Fvar f ->
      f

(* Specialize *)

let find_type_var ~loc env tv =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_ty_decl_var ~loc ~user:false tv in
    Htv.add env tv v;
    v
 
let rec specialize_ty ~loc env t = match t.ty_node with
  | Ty.Tyvar tv -> 
      Tyvar (find_type_var ~loc env tv)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize_ty ~loc env) tl)

let specialize_lsymbol ~loc s =
  let tl = s.ls_args in
  let t = s.ls_value in
  let env = Htv.create 17 in
  List.map (specialize_ty ~loc env) tl, option_map (specialize_ty ~loc env) t

let rec specialize_pattern ~loc htv p = 
  { dp_node = specialize_pattern_node  ~loc htv p.pat_node;
    dp_ty   = specialize_ty           ~loc htv p.pat_ty; }

and specialize_pattern_node ~loc htv = function
  | Term.Pwild -> 
      Pwild
  | Term.Pvar v ->
      Pvar v.vs_name.id_string
  | Term.Papp (s, pl) ->
      Papp (s, List.map (specialize_pattern ~loc htv) pl)
  | Term.Pas (p, v) ->
      Pas (specialize_pattern ~loc htv p, v.vs_name.id_string)

let rec specialize_term ~loc htv t =  
  { dt_node = specialize_term_node  ~loc htv t.t_node;
    dt_ty   = specialize_ty        ~loc htv t.t_ty; }

and specialize_term_node ~loc htv = function
  | Term.Tbvar _ ->
      assert false
  | Term.Tvar v -> 
      Tvar v.vs_name.id_string (* TODO: correct? is capture possible? *)
  | Term.Tconst c ->
      Tconst c
  | Term.Tapp (ls, tl) ->
      Tapp (ls, List.map (specialize_term ~loc htv) tl)
  | Term.Tif (f, t1, t2) ->
      Tif (specialize_fmla ~loc htv f, 
	   specialize_term ~loc htv t1, specialize_term ~loc htv t2)
  | Term.Tlet (t1, t2) ->
      let v, t2 = t_open_bound t2 in 
      Tlet (specialize_term ~loc htv t1, 
	    v.vs_name.id_string, specialize_term ~loc htv t2)
  | Term.Tcase (tl, bl) ->
      let branch b = 
	let pl, t = t_open_branch b in 
	List.map (specialize_pattern ~loc htv) pl, specialize_term ~loc htv t
      in
      Tmatch (List.map (specialize_term ~loc htv) tl, List.map branch bl)
  | Term.Teps fb ->
      let v, f = f_open_bound fb in
      Teps (v.vs_name.id_string, specialize_ty ~loc htv v.vs_ty,
	    specialize_fmla ~loc htv f)

(* TODO: labels are lost *)
and specialize_fmla ~loc htv f = match f.f_node with
  | Term.Fapp (ls, tl) ->
      Fapp (ls, List.map (specialize_term ~loc htv) tl)
  | Term.Fquant (q, fq) ->
      let vl, tl, f = f_open_quant fq in
      let uquant v = v.vs_name.id_string, specialize_ty ~loc htv v.vs_ty in
      let tl = List.map (List.map (specialize_trigger ~loc htv)) tl in
      Fquant (q, List.map uquant vl, tl, specialize_fmla ~loc htv f)
  | Term.Fbinop (b, f1, f2) ->
      Fbinop (b, specialize_fmla ~loc htv f1, specialize_fmla ~loc htv f2)
  | Term.Fnot f1 ->
      Fnot (specialize_fmla ~loc htv f1)
  | Term.Ftrue ->
      Ftrue
  | Term.Ffalse ->
      Ffalse
  | Term.Fif (f1, f2, f3) ->
      Fif (specialize_fmla ~loc htv f1, 
	   specialize_fmla ~loc htv f2, specialize_fmla ~loc htv f3)
  | Term.Flet (t1, f2b) ->
      let v, f2 = f_open_bound f2b in
      Flet (specialize_term ~loc htv t1,
	    v.vs_name.id_string, specialize_fmla ~loc htv f2)
  | Term.Fcase (tl, fbl) ->
      let branch b = 
       let pl, f = f_open_branch b in 
	List.map (specialize_pattern ~loc htv) pl, specialize_fmla ~loc htv f
     in
     Fmatch (List.map (specialize_term ~loc htv) tl, List.map branch fbl)

and specialize_trigger ~loc htv = function
  | Term.Term t -> TRterm (specialize_term ~loc htv t)
  | Term.Fmla f -> TRfmla (specialize_fmla ~loc htv f)


