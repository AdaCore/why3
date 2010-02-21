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
  | Message of string
  | ClashType of string
  | BadTypeArity of string
  | UnboundType of qualid
  | TypeArity of qualid * int * int
  | Clash of string
  | PredicateExpected
  | TermExpected
  | UnboundSymbol of qualid
  | TermExpectedType of (formatter -> unit) * (formatter -> unit) 
      (* actual / expected *)
  | BadNumberOfArguments of Name.t * int * int 
  | ClashTheory of string
  | UnboundTheory of string
  | AlreadyTheory of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let rec print_qualid fmt = function
  | Qident s -> fprintf fmt "%s" s.id
  | Qdot (m, s) -> fprintf fmt "%a.%s" print_qualid m s.id

let report fmt = function
  | Message s ->
      fprintf fmt "%s" s
  | ClashType s ->
      fprintf fmt "clash with previous type %s" s
  | BadTypeArity s ->
      fprintf fmt "duplicate type parameter %s" s
  | UnboundType s ->
       fprintf fmt "Unbound type '%a'" print_qualid s
  | TypeArity (id, a, n) ->
      fprintf fmt "@[The type %a expects %d argument(s),@ " print_qualid id a;
      fprintf fmt "but is applied to %d argument(s)@]" n
  | Clash id ->
      fprintf fmt "Clash with previous constant %s" id
  | PredicateExpected ->
      fprintf fmt "syntax error: predicate expected"
  | TermExpected ->
      fprintf fmt "syntax error: term expected"
  | UnboundSymbol s ->
       fprintf fmt "Unbound symbol '%a'" print_qualid s
  | BadNumberOfArguments (s, n, m) ->
      fprintf fmt "@[Symbol `%a' is aplied to %d terms,@ " Name.print s n;
      fprintf fmt "but is expecting %d arguments@]" m
  | TermExpectedType (ty1, ty2) ->
      fprintf fmt "@[This term has type "; ty1 fmt; 
      fprintf fmt "@ but is expected to have type@ "; ty2 fmt; fprintf fmt "@]"
  | ClashTheory s ->
      fprintf fmt "clash with previous theory %s" s
  | UnboundTheory s ->
      fprintf fmt "unbound theory %s" s
  | AlreadyTheory s ->
      fprintf fmt "already using a theory with name %s" s

(** typing environments *)

module M = Map.Make(String)

type env = {
  tysymbols : tysymbol M.t; (* type symbols *)
  fsymbols  : fsymbol M.t;  (* function symbols *)
  psymbols  : psymbol M.t;  (* predicate symbols *)
  theories  : env M.t;      (* theories (including "self") *)
}

let empty = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  theories  = M.empty;
}

let find_tysymbol s env = M.find s.id env.tysymbols
let find_fsymbol s env = M.find s.id env.fsymbols
let find_psymbol s env = M.find s.id env.psymbols

let loaded_theories = Hashtbl.create 17

let add_tysymbol x ty env = { env with tysymbols = M.add x ty env.tysymbols }
let add_fsymbol x ty env = { env with fsymbols = M.add x ty env.fsymbols }
let add_psymbol x ty env = { env with psymbols = M.add x ty env.psymbols }
let add_theory x t env = { env with theories = M.add x t env.theories }

let self_id = "(*self*)"

let add_self f ?(self=true) x v env = 
  if self then
    f x v { env with theories = 
        M.add self_id (f x v (M.find self_id env.theories)) env.theories }
  else 
    f x v env

let add_tysymbol = add_self add_tysymbol
let add_fsymbol  = add_self add_fsymbol
let add_psymbol  = add_self add_psymbol
let add_theory   = add_self add_theory

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
 
(* Specialize *)

module Htv = Hashtbl.Make(Name)

let find_type_var env tv =
  try
    Htv.find env tv
  with Not_found ->
    let v = create_type_var ~user:false tv in
    Htv.add env tv v;
    v
 
let rec specialize env t = match t.Ty.ty_node with
  | Ty.Tyvar tv -> 
      Tyvar (find_type_var env tv)
  | Ty.Tyapp (s, tl) ->
      Tyapp (s, List.map (specialize env) tl)

let find_local_theory t env = 
  try M.find t.id env.theories
  with Not_found -> error ~loc:t.id_loc (UnboundTheory t.id)

let find_global_theory t =
  try Hashtbl.find loaded_theories t.id
  with Not_found -> error ~loc:t.id_loc (UnboundTheory t.id)

let rec find_theory q env = match q with
  | Qident t -> find_local_theory t env
  | Qdot (q, t) -> let env = find_theory q env in find_local_theory t env

let rec find f q env = match q with
  | Qident x -> f x env
  | Qdot (m, x) -> let env = find_theory m env in f x env

let specialize_tysymbol x env =
  let s = find find_tysymbol x env.env in
  let env = Htv.create 17 in
  s, List.map (find_type_var env) s.Ty.ts_args
	
let specialize_fsymbol x env =
  let s = find find_fsymbol x env.env in
  let tl, t = s.fs_scheme in
  let env = Htv.create 17 in
  s, List.map (specialize env) tl, specialize env t

let specialize_psymbol x env =
  let s = find find_psymbol x env.env in
  let env = Htv.create 17 in
  s, List.map (specialize env) s.ps_scheme

(** Typing types *)

let rec qloc = function
  | Qident x -> x.id_loc
  | Qdot (m, x) -> Loc.join (qloc m) x.id_loc

(* parsed types -> intermediate types *)
let rec dty env = function
  | PPTtyvar {id=x} -> 
      Tyvar (find_user_type_var x env)
  | PPTtyapp (p, x) ->
      let loc = qloc x in
      let s, tv = 
	try specialize_tysymbol x env
	with Not_found -> error ~loc:loc (UnboundType x)
      in
      let np = List.length p in
      let a = List.length tv in
      if np <> a then error ~loc (TypeArity (x, a, np));
      Tyapp (s, List.map (dty env) p)

(* intermediate types -> types *)
let rec ty = function
  | Tyvar { type_val = Some t } ->
      ty t
  | Tyvar { tvsymbol = tv } ->
      Ty.ty_var tv
  | Tyapp (s, tl) ->
      Ty.ty_app s (List.map ty tl)

(** Typing terms and formulas *)

type dterm = { dt_node : dterm_node; dt_ty : dty }

and dterm_node =
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
  | PPvar (Qident {id=x}) when M.mem x env.dvars ->
      (* local variable *)
      let ty = M.find x env.dvars in
      Tvar x, ty
  | PPvar x -> 
      (* 0-arity symbol (constant) *)
      begin try 
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
  | PPforall ({id=x}, ty, _, a) -> (* TODO: triggers *)
      let ty = dty env ty in
      let env = { env with dvars = M.add x ty env.dvars } in
      Fquant (Fforall, x, ty, dfmla env a)
  | PPexists ({id=x}, ty, a) -> (* TODO: triggers *)
      let ty = dty env ty in
      let env = { env with dvars = M.add x ty env.dvars } in
      Fquant (Fexists, x, ty, dfmla env a)
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
  | _ ->
      assert false (* TODO *)

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

let add_type loc sl s env =
  if M.mem s.id env.tysymbols then error ~loc (ClashType s.id);
  let tyvars = ref M.empty in
  let add_ty_var {id=x} =
    if M.mem x !tyvars then error ~loc (BadTypeArity x);
    let v = Name.from_string x in
    tyvars := M.add x v !tyvars;
    v
  in
  let vl = List.map add_ty_var sl in
  let ty = Ty.create_tysymbol (Name.from_string s.id) vl None in
  add_tysymbol s.id ty env

let add_function loc pl t env {id=id} =
  if M.mem id env.fsymbols then error ~loc (Clash id);
  let denv = create_denv env in
  let pl = List.map (dty denv) pl and t = dty denv t in
  let pl = List.map ty pl and t = ty t in
  let s = create_fsymbol (Name.from_string id) (pl, t) false in
  add_fsymbol id s env

let add_predicate loc pl env {id=id} =
  if M.mem id env.psymbols then error ~loc (Clash id);
  let denv = create_denv env in
  let pl = List.map (dty denv) pl in
  let pl = List.map ty pl in
  let s = create_psymbol (Name.from_string id) pl in
  add_psymbol id s env

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

let uses_theory env (as_t, q) =
  let loc = qloc q in
  let rec find_theory q = match q with
    | Qident t -> 
	t.id, find_global_theory t
    | Qdot (q, t) -> 
	let _, env = find_theory q in t.id, find_local_theory t env
  in
  let id, th = find_theory q in
  let id = match as_t with None -> id | Some x -> x.id in
  if M.mem id env.theories then error ~loc (AlreadyTheory id);
  add_theory id th env

let open_theory t env =
  let loc = t.id_loc and id = t.id in
  if not (M.mem id env.theories) then error ~loc (UnboundTheory id);
  let th = M.find id env.theories in
  let open_map m1 m2 = M.fold M.add m1 m2 in
  { tysymbols = open_map th.tysymbols env.tysymbols;
    fsymbols  = open_map th.fsymbols  env.fsymbols;
    psymbols  = open_map th.psymbols  env.psymbols;
    theories  = open_map th.theories  env.theories }

let rec add_decl env = function
  | TypeDecl (loc, sl, s) ->
      add_type loc sl s env
  | Logic (loc, ids, PPredicate pl) ->
      List.fold_left (add_predicate loc pl) env ids
  | Logic (loc, ids, PFunction (pl, t)) ->
      List.fold_left (add_function loc pl t) env ids
  | Axiom (loc, s, f) ->
      axiom loc s f env
  | Theory th ->
      add_theory th env
  | Uses (loc, uses) ->
      List.fold_left uses_theory env uses
  | Open id ->
      open_theory id env
  | AlgType _ 
  | Goal _ 
  | Function_def _ 
  | Predicate_def _ 
  | Inductive_def _ ->
      assert false (*TODO*)


and add_decls env = List.fold_left add_decl env

and add_theory th env =
  let id = th.th_name.id in
  if Hashtbl.mem loaded_theories id then error ~loc:th.th_loc (ClashTheory id);
  let th_env = { empty with theories = M.add self_id empty M.empty } in
  let th_env = add_decls th_env th.th_decl in
  Hashtbl.add loaded_theories id (M.find self_id th_env.theories);
  env

(*
Local Variables: 
compile-command: "make -C .. test"
End: 
*)
