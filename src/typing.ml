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

open Util
open Format
open Pp
open Term
open Ptree

(** errors *)

type error = 
  | ClashType of string
  | BadTypeArity of string
  | UnboundType of string
  | TypeArity of string * int * int
  | Clash of string
  | PredicateExpected
  | TermExpected
  | UnboundSymbol of string
  | TermExpectedType of (formatter -> unit) * (formatter -> unit) 
      (* actual / expected *)
  | BadNumberOfArguments of Name.t * int * int 
  | ClashTheory of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let report fmt = function
  | ClashType s ->
      fprintf fmt "clash with previous type %s" s
  | BadTypeArity s ->
      fprintf fmt "duplicate type parameter %s" s
  | UnboundType s ->
       fprintf fmt "Unbound type '%s'" s
  | TypeArity (id, a, n) ->
      fprintf fmt "@[The type %s expects %d argument(s),@ " id a;
      fprintf fmt "but is applied to %d argument(s)@]" n
  | Clash id ->
      fprintf fmt "Clash with previous constant %s" id
  | PredicateExpected ->
      fprintf fmt "syntax error: predicate expected"
  | TermExpected ->
      fprintf fmt "syntax error: term expected"
  | UnboundSymbol s ->
       fprintf fmt "Unbound symbol '%s'" s
  | BadNumberOfArguments (s, n, m) ->
      fprintf fmt "@[Symbol `%a' is aplied to %d terms,@ " Name.print s n;
      fprintf fmt "but is expecting %d arguments@]" m
  | TermExpectedType (ty1, ty2) ->
      fprintf fmt "@[This term has type "; ty1 fmt; 
      fprintf fmt "@ but is expected to have type@ "; ty2 fmt; fprintf fmt "@]"
  | ClashTheory s ->
      fprintf fmt "clash with previous theory %s" s

(** typing environments *)

module M = Map.Make(String)

type env = {
  tysymbols : tysymbol M.t; (* type symbols *)
  fsymbols  : fsymbol M.t;  (* function symbols *)
  psymbols  : psymbol M.t;  (* predicate symbols *)
  theories  : env M.t;
}

let empty = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  theories  = M.empty;
}

let is_empty env = 
  M.is_empty env.tysymbols &&
  M.is_empty env.fsymbols &&
  M.is_empty env.psymbols

let find_tysymbol s env = M.find s env.tysymbols
let find_fsymbol s env = M.find s env.fsymbols
let find_psymbol s env = M.find s env.psymbols

let add_tysymbol x ty env = { env with tysymbols = M.add x ty env.tysymbols }


(** typing using destructive type variables 

    parsed trees        intermediate trees       typed trees
      (Ptree)               (D below)               (Term)
   -----------------------------------------------------------
     ppure_type  ---dty--->   dty       ---ty--->    ty
      lexpr      --dterm-->   dterm     --term-->    term
      lexpr      --dfmla-->   dfmla     --fmla-->    fmla

*)

(** types with destructive type variables *)

type dty =
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list
      
and type_var = { 
  tag : int; 
  user : bool;
  tvsymbol : tvsymbol;
  mutable type_val : dty option;
}

let rec print_dty fmt = function
  | Tyvar { type_val = Some t } ->
      print_dty fmt t
  | Tyvar { type_val = None; tvsymbol = v } ->
      fprintf fmt "'%a" Name.print v
  | Tyapp (s, []) ->
      fprintf fmt "%a" Name.print s.Ty.ts_name
  | Tyapp (s, [t]) -> 
      fprintf fmt "%a %a" print_dty t Name.print s.Ty.ts_name
  | Tyapp (s, l) -> 
      fprintf fmt "(%a) %a" 
	(print_list comma print_dty) l Name.print s.Ty.ts_name

let create_type_var =
  let t = ref 0 in
  fun ~user tv -> 
    incr t; 
    { tag = !t; user = user; tvsymbol = tv; type_val = None }

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
      s1 == s2 && List.length l1 = List.length l2 &&
	  List.for_all2 unify l1 l2
  | Tyapp _, _ | _, Tyapp _ ->
      false
	(* other cases *)
  | Tyvar {user=true; tag=t1}, Tyvar {user=true; tag=t2} -> 
      t1 = t2

(** Destructive typing environment, that is
    environment + local variables.
    It is only local to this module and created with [create_denv] below. *)

type denv = { 
  env : env;
  utyvars : (string, type_var) Hashtbl.t; (* user type variables *)
  dvars : dty M.t; (* local variables, to be bound later *)
}

let create_denv env = { 
  env = env; 
  utyvars = Hashtbl.create 17; 
  dvars = M.empty;
}

let find_user_type_var x env =
  try
    Hashtbl.find env.utyvars x
  with Not_found ->
    let v = create_type_var ~user:true (Name.from_string x) in
    Hashtbl.add env.utyvars x v;
    v
 
(** Typing types *)

(* parsed types -> intermediate types *)
let rec dty env = function
  | PPTvarid (x, _) -> 
      Tyvar (find_user_type_var x env)
  | PPTexternal (p, id, loc) ->
      if not (M.mem id env.env.tysymbols) then error ~loc (UnboundType id);
      let s = M.find id env.env.tysymbols in
      let np = List.length p in
      let a = List.length s.Ty.ts_args in
      if np <> a then error ~loc (TypeArity (id, a, np));
      Tyapp (s, List.map (dty env) p)

(* intermediate types -> types *)
let rec ty = function
  | Tyvar { type_val = Some t } ->
      ty t
  | Tyvar { tvsymbol = tv } ->
      Ty.ty_var tv
  | Tyapp (s, tl) ->
      Ty.ty_app s (List.map ty tl)

(* Specialize *)

module Htv = Hashtbl.Make(Name)

let find_type_var tv env =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_type_var ~user:false tv in
    Htv.add env tv v;
    v
 
let rec specialize env t = match t.Ty.ty_node with
  | Ty.Tyvar tv -> 
      Tyvar (find_type_var tv env)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize env) tl)
	
let specialize_fsymbol x env =
  let s = find_fsymbol x env.env in
  let tl, t = s.fs_scheme in
  let env = Htv.create 17 in
  s, List.map (specialize env) tl, specialize env t

let specialize_psymbol x env =
  let s = find_psymbol x env.env in
  let env = Htv.create 17 in
  s, List.map (specialize env) s.ps_scheme

(** Typing terms and formulas *)

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
  | Tbvar of int
  | Tvar of string
  | Tapp of fsymbol * dterm list
  | Tlet of dterm * string * dterm
(*   | Tcase of dterm * tbranch list *)
  | Teps of string * dfmla

and dfmla = 
  | Fapp of psymbol * dterm list
  | Fquant of quant * string * dty * dfmla
  | Fbinop of binop * dfmla * dfmla
  | Fnot of dfmla
  | Ftrue
  | Ffalse
  | Fif of dfmla * dfmla * dfmla
(*   | Flet of dterm * string * dfmla *)
(*   | Fcase of dterm * (pattern * dfmla) list *)

let binop = function
  | PPand -> Fand
  | PPor -> For
  | PPimplies -> Fimplies
  | PPiff -> Fiff
  | _ -> assert false 

let rec dterm env t = 
  let n, ty = dterm_node t.pp_loc env t.pp_desc in
  { dt_node = n; dt_ty = ty }

and dterm_node loc env = function
  | PPvar x ->
      begin try
	(* local variable *)
	let ty = M.find x env.dvars in
	Tvar x, ty
      with Not_found -> try 
	(* 0-arity symbol (constant) *)
	let s, tyl, ty = specialize_fsymbol x env in
	let n = List.length tyl in
	if n > 0 then error ~loc (BadNumberOfArguments (s.fs_name, 0, n));
	Tapp (s, []), ty
      with Not_found -> 
	error ~loc (UnboundSymbol x)
      end
  | PPapp (x, tl) ->
      begin try
	let s, tyl, ty = specialize_fsymbol x env in
	let tl = dtype_args s.fs_name loc env tyl tl in
	Tapp (s, tl), ty
      with Not_found ->
	error ~loc (UnboundSymbol x)
      end
  | _ ->
      assert false (*TODO*)

and dfmla env e = match e.pp_desc with
  | PPtrue ->
      Ftrue
  | PPfalse ->
      Ffalse
  | PPprefix (PPnot, a) ->
      Fnot (dfmla env a)
  | PPinfix (a, (PPand | PPor | PPimplies | PPiff as op), b) ->
      Fbinop (binop op, dfmla env a, dfmla env b)
  | PPinfix _ ->
      error ~loc:e.pp_loc PredicateExpected
  | PPif (a, b, c) ->
      Fif (dfmla env a, dfmla env b, dfmla env c)  
  | PPforall (id, ty, _, a) -> (* TODO: triggers *)
      let ty = dty env ty in
      let env = { env with dvars = M.add id ty env.dvars } in
      Fquant (Fforall, id, ty, dfmla env a)
  | PPexists (id, ty, a) -> (* TODO: triggers *)
      let ty = dty env ty in
      let env = { env with dvars = M.add id ty env.dvars } in
      Fquant (Fexists, id, ty, dfmla env a)
  | PPapp (x, tl) ->
      let s, tyl = 
	try 
	  specialize_psymbol x env 
	with Not_found -> 
	  error ~loc:e.pp_loc (UnboundSymbol x)
      in
      let tl = dtype_args s.ps_name e.pp_loc env tyl tl in
      Fapp (s, tl)
  | _ ->
      assert false (*TODO*)

and dtype_args s loc env el tl =
  let n = List.length el and m = List.length tl in
  if n <> m then error ~loc (BadNumberOfArguments (s, m, n));
  let rec check_arg = function
    | [], [] -> 
	[]
    | a :: al, t :: bl ->
	let loc = t.pp_loc in
	let t = dterm env t in
	if not (unify a t.dt_ty) then
	  error ~loc (TermExpectedType ((fun f -> print_dty f t.dt_ty),
					(fun f -> print_dty f a)));
	t :: check_arg (al, bl)
    | _ ->
	assert false
  in
  check_arg (el, tl)

let rec term env t = match t.dt_node with
  | Tvar x ->
      assert (M.mem x env);
      t_var (M.find x env)
  | Tapp (s, tl) ->
      t_app s (List.map (term env) tl) (ty t.dt_ty)

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
  | Fquant (q, x, t, f1) ->
      let v = create_vsymbol (Name.from_string x) (ty t) in
      let env = M.add x v env in
      f_quant q v (fmla env f1)
  | Fapp (s, tl) ->
      f_app s (List.map (term env) tl)


(** Typing declarations, that is building environments. *)

open Ptree

let add_type loc ext sl s env =
  if M.mem s env.tysymbols then error ~loc (ClashType s);
  let tyvars = ref M.empty in
  let add_ty_var x =
    if M.mem x !tyvars then error ~loc (BadTypeArity x);
    let v = Name.from_string x in
    tyvars := M.add x v !tyvars;
    v
  in
  let vl = List.map add_ty_var sl in
  let ty = Ty.create_tysymbol (Name.from_string s) vl None in
  add_tysymbol s ty env

let add_function loc pl t env id =
  if M.mem id env.fsymbols then error ~loc (Clash id);
  let denv = create_denv env in
  let pl = List.map (dty denv) pl and t = dty denv t in
  let pl = List.map ty pl and t = ty t in
  let s = create_fsymbol (Name.from_string id) (pl, t) false in
  { env with fsymbols = M.add id s env.fsymbols }

let add_predicate loc pl env id =
  if M.mem id env.psymbols then error ~loc (Clash id);
  let denv = create_denv env in
  let pl = List.map (dty denv) pl in
  let pl = List.map ty pl in
  let s = create_psymbol (Name.from_string id) pl in
  { env with psymbols = M.add id s env.psymbols }

let fmla env f =
  let denv = create_denv env in
  let f = dfmla denv f in
  fmla M.empty f

let term env t =
  let denv = create_denv env in
  let t = dterm denv t in
  term M.empty t

let axiom loc s f env =
  ignore (fmla env f);
  env

let rec add_decl env = function
  | TypeDecl (loc, ext, sl, s) ->
      add_type loc ext sl s env
  | Logic (loc, ext, ids, PPredicate pl) ->
      List.fold_left (add_predicate loc pl) env ids
  | Logic (loc, ext, ids, PFunction (pl, t)) ->
      List.fold_left (add_function loc pl t) env ids
  | Axiom (loc, s, f) ->
      axiom loc s f env
  | Theory (loc, s, u, dl) ->
      add_theory loc s u dl env
  | _ ->
      assert false (*TODO*)

and add_decls env = List.fold_left add_decl env

and add_theory loc s u dl env =
  assert (is_empty env);
  if M.mem s env.theories then error ~loc (ClashTheory s);
  let env = add_decls env dl in
  { empty with theories = M.add s env env.theories }

