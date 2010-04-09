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
open Why
open Util
open Ident
open Term
open Theory
open Denv
open Ptree
open Pgm_ttree

type error =
  | Message of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (Message s))
    fmt f

let report fmt = function
  | Message s ->
      fprintf fmt "%s" s

(*** from Typing *************************************************************)
type denv = {
  uc : theory_uc;
  denv : Typing.denv;
  (* predefined symbols from theory programs.Prelude *)
  ty_bool  : dty;
  ty_unit  : dty;
  ts_arrow : Ty.tysymbol;
}

let create_denv uc = 
  let ns = get_namespace uc in
  { uc = uc;
    denv = Typing.create_denv uc;
    ty_bool  = Tyapp (ns_find_ts ns ["bool"], []);
    ty_unit  = Tyapp (ns_find_ts ns ["unit"], []);
    ts_arrow = ns_find_ts ns ["arrow"];

  }
(*****************************************************************************)

let create_type_var loc =
  let tv = Ty.create_tvsymbol (id_user "a" loc) in
  Tyvar (create_ty_decl_var ~loc ~user:false tv)

let currying env tyl ty =
  let make_arrow_type ty1 ty2 = Tyapp (env.ts_arrow, [ty1; ty2]) in
  List.fold_right make_arrow_type tyl ty

let expected_type e ty =
  if not (Denv.unify e.dexpr_type ty) then
    errorm ~loc:e.dexpr_loc 
      "this expression has type %a, but is expected to have type %a"
      print_dty e.dexpr_type print_dty ty

(* phase 1: typing programs (using destructive type inference) *)

let pure_type env = Typing.dty env.denv

let rec dtype_v env = function
  | Pgm_ptree.Tpure pt -> DTpure (pure_type env pt)

let rec dexpr env e = 
  let d, ty = expr_desc env e.Pgm_ptree.expr_loc e.Pgm_ptree.expr_desc in
  { dexpr_desc = d; dexpr_loc = e.Pgm_ptree.expr_loc;
    dexpr_denv = env.denv; dexpr_type = ty;  }

and expr_desc env loc = function
  | Pgm_ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, Tyapp (Ty.ts_int, [])
  | Pgm_ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, Tyapp (Ty.ts_real, [])
  | Pgm_ptree.Eident (Qident {id=x}) when Typing.mem_var x env.denv ->
      (* local variable *)
      let ty = Typing.find_var x env.denv in
      DElocal x, ty
  | Pgm_ptree.Eident p ->
      let s, tyl, ty = Typing.specialize_fsymbol p env.uc in
      DEglobal s, currying env tyl ty
  | Pgm_ptree.Eapply (e1, e2) ->
      let e1 = dexpr env e1 in
      let e2 = dexpr env e2 in
      begin match e1.dexpr_type with
	| Tyapp (ts, [ty2; ty]) when ts == env.ts_arrow ->
	    expected_type e2 ty2;
	    DEapply (e1, e2), ty
	| _ ->
	    errorm ~loc:e1.dexpr_loc "this expression is not a function"
      end
  | Pgm_ptree.Elet ({id=x}, e1, e2) ->
      let e1 = dexpr env e1 in
      let ty1 = e1.dexpr_type in
      let env = { env with denv = Typing.add_var x ty1 env.denv } in
      let e2 = dexpr env e2 in
      DElet (x, e1, e2), e2.dexpr_type

  | Pgm_ptree.Esequence (e1, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 env.ty_unit;
      let e2 = dexpr env e2 in
      DEsequence (e1, e2), e2.dexpr_type
  | Pgm_ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr env e1 in
      expected_type e1 env.ty_bool;
      let e2 = dexpr env e2 in
      let e3 = dexpr env e3 in
      expected_type e3 e2.dexpr_type;
      DEif (e1, e2, e3), e2.dexpr_type
  | Pgm_ptree.Ewhile (e1, a, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 env.ty_bool;
      let e2 = dexpr env e2 in
      expected_type e2 env.ty_unit;
      DEwhile (e1, a, e2), env.ty_unit
  | Pgm_ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 env.ty_bool;
      let e2 = dexpr env e2 in
      expected_type e2 env.ty_bool;
      DElazy (op, e1, e2), env.ty_bool
  | Pgm_ptree.Ematch (el, bl) ->
      assert false (*TODO*)
  | Pgm_ptree.Eskip ->
      DEskip, env.ty_unit
  | Pgm_ptree.Eabsurd ->
      DEabsurd, create_type_var loc

  | Pgm_ptree.Eassert (k, le) ->
      DEassert (k, le), env.ty_unit
  | Pgm_ptree.Eghost e1 ->
      let e1 = dexpr env e1 in
      DEghost e1, e1.dexpr_type
  | Pgm_ptree.Elabel ({id=l}, e1) ->
      (* TODO: add label to env *)
      let e1 = dexpr env e1 in
      DElabel (l, e1), e1.dexpr_type
  | Pgm_ptree.Ecast (e1, ty) ->
      let e1 = dexpr env e1 in
      let ty = pure_type env ty in
      expected_type e1 ty;
      e1.dexpr_desc, ty

(* phase 2: typing annotations *)

let rec expr env e =
  let d = expr_desc env e.dexpr_denv e.dexpr_desc in
  let ty = Denv.ty_of_dty e.dexpr_type in
  { expr_desc = d; expr_type = ty; expr_loc = e.dexpr_loc }

and expr_desc env denv = function
  | DEconstant c ->
      Econstant c
  | DElocal x ->
      Elocal (Mstr.find x env)
  | DEglobal ls ->
      Eglobal ls
  | DEapply (e1, e2) ->
      Eapply (expr env e1, expr env e2)
  | DElet (x, e1, e2) ->
      let e1 = expr env e1 in
      let v = create_vsymbol (id_fresh x) e1.expr_type in
      let env = Mstr.add x v env in
      Elet (v, e1, expr env e2)

  | DEsequence (e1, e2) ->
      Esequence (expr env e1, expr env e2)
  | DEif (e1, e2, e3) ->
      Eif (expr env e1, expr env e2, expr env e3)
  | DEwhile (e1, la, e2) ->
      let la = 
	{ loop_invariant = 
	    option_map (Typing.type_fmla denv env) la.Pgm_ptree.loop_invariant;
	  loop_variant   = 
	    option_map (Typing.type_term denv env) la.Pgm_ptree.loop_variant; }
      in
      Ewhile (expr env e1, la, expr env e2)
  | DElazy (op, e1, e2) ->
      Elazy (op, expr env e1, expr env e2)
  | DEskip ->
      Eskip
  | DEabsurd ->
      Eabsurd

  | DEassert (k, f) ->
      let f = Typing.type_fmla denv env f in
      Eassert (k, f)
  | DEghost e1 -> 
      Eghost (expr env e1)
  | DElabel (s, e1) ->
      Elabel (s, expr env e1)

let code uc id e =
  let env = create_denv uc in
  let e = dexpr env e in
  ignore (expr Mstr.empty e)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
