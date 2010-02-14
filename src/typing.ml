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
open Term
open Ptree

(** errors *)

type error = 
  | ClashType of string
  | BadTypeArity of string
  | UnboundType of string
  | TypeArity of string * int * int
  | Clash of string

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

module M = Map.Make(String)

type env = {
  tysymbols : tysymbol M.t;
  fsymbols  : fsymbol M.t;
  psymbols  : psymbol M.t;
  tyvars    : tvsymbol M.t;
  vars      : vsymbol M.t;
}

let empty = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  tyvars    = M.empty;
  vars      = M.empty;
}

let find_tysymbol s env = M.find s env.tysymbols
let find_fsymbol s env = M.find s env.fsymbols
let find_psymbol s env = M.find s env.psymbols
let find_tyvar s env = M.find s env.tyvars
let find_var s env = M.find s env.vars

let add_tyvar x v env = { env with tyvars = M.add x v env.tyvars}
let add_tysymbol x ty env = { env with tysymbols = M.add x ty env.tysymbols }


(** typing using destructive type variables *)

module D = struct

  (* types with destructive type variables *)
  type ty =
    | Tyvar of type_var
    | Tyapp of tysymbol * ty list

  and type_var = { 
    tag : int; 
    user : bool;
    tvsymbol : tvsymbol;
    mutable type_val : ty option;
  }

  let create_type_var =
    let t = ref 0 in
    fun ~user x -> 
      incr t; 
      { tag = !t; user = user; tvsymbol = Name.from_string x; type_val = None }

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

  (* env + destructive type variables environment *)
  type denv = { 
    env : env;
    dvars : (string, type_var) Hashtbl.t;
  }

  let create env = { env = env; dvars = Hashtbl.create 17 }

  let find_type_var x env =
    try
      Hashtbl.find env.dvars x
    with Not_found ->
      let v = create_type_var ~user:true x in
      Hashtbl.add env.dvars x v;
      v
 
  (* parsed types -> intermediate types *)
  let rec dty env = function
    | PPTvarid (x, _) -> 
	Tyvar (find_type_var x env)
    | PPTexternal (p, id, loc) ->
	if not (M.mem id env.env.tysymbols) then error ~loc (UnboundType id);
	let s = M.find id env.env.tysymbols in
	let np = List.length p in
	let a = List.length s.Ty.ts_args in
	if np <> a then error ~loc (TypeArity (id, a, np));
	Tyapp (s, List.map (dty env) p)

  (* intermediate types -> types *)
  let rec ty env = function
    | Tyvar { type_val = Some t } ->
	ty env t
    | Tyvar { tvsymbol = tv } ->
	Ty.ty_var tv
    | Tyapp (s, tl) ->
	Ty.ty_app s (List.map (ty env) tl)
	

end

(** typing *)

let term env t = match t.pp_desc with
  | _ ->
      assert false (*TODO*)


let fmla env f =
  assert false (*TODO*)

(** building environments *)

open Ptree

let add_type loc ext sl s env =
  if M.mem s env.tysymbols then error ~loc (ClashType s);
  let add_ty_var env x =
    if M.mem x env.tyvars then error ~loc (BadTypeArity x);
    let v = Name.from_string x in
    add_tyvar x v env, v
  in
  let _, vl = map_fold_left add_ty_var env sl in
  let ty = Ty.create_tysymbol (Name.from_string s) vl None in
  add_tysymbol s ty env

let add_function loc pl t env id =
  if M.mem id env.fsymbols then error ~loc (Clash id);
  let denv = D.create env in
  let pl = List.map (D.dty denv) pl and t = D.dty denv t in
  let pl = List.map (D.ty denv) pl and t = D.ty denv t in
  let s = create_fsymbol (Name.from_string id) (pl, t) false in
  { env with fsymbols = M.add id s env.fsymbols }

let add_predicate loc pl env id =
  if M.mem id env.psymbols then error ~loc (Clash id);
  let denv = D.create env in
  let pl = List.map (D.dty denv) pl in
  let pl = List.map (D.ty denv) pl in
  let s = create_psymbol (Name.from_string id) pl in
  { env with psymbols = M.add id s env.psymbols }

let add env = function
  | TypeDecl (loc, ext, sl, s) ->
      add_type loc ext sl s env
  | Logic (loc, ext, ids, PPredicate pl) ->
      List.fold_left (add_predicate loc pl) env ids
  | Logic (loc, ext, ids, PFunction (pl, t)) ->
      List.fold_left (add_function loc pl t) env ids
  | _ ->
      assert false (*TODO*)
