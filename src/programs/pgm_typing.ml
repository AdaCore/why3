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
open Util
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
  utyvars : (string, type_var) Hashtbl.t;
  dvars : dty Mstr.t;
  (* predefined symbols, from theory programs.Prelude *)
  ts_bool  : Ty.tysymbol;
  ts_unit  : Ty.tysymbol;
  ts_arrow : Ty.tysymbol;
}

let create_denv uc = 
  let ns = get_namespace uc in
  { uc = uc;
    utyvars = Hashtbl.create 17;
    dvars = Mstr.empty;
    ts_bool  = ns_find_ts ns ["Prelude"; "bool"];
    ts_unit  = ns_find_ts ns ["Prelude"; "unit"];
    ts_arrow = ns_find_ts ns ["Prelude"; "arrow"];
  }
(*****************************************************************************)

let currying env tyl ty =
  let make_arrow_type ty1 ty2 = Tyapp (env.ts_arrow, [ty1; ty2]) in
  List.fold_right make_arrow_type tyl ty

let expected_type e ty =
  if not (Denv.unify e.expr_type ty) then
    errorm ~loc:e.expr_loc 
      "this expression has type %a, but is expected to have type %a"
      print_dty e.expr_type print_dty ty

let rec expr env e = 
  let d, ty = expr_desc env e.Pgm_ptree.expr_loc e.Pgm_ptree.expr_desc in
  { expr_desc = d; expr_type = ty; expr_loc = e.Pgm_ptree.expr_loc }

and expr_desc env loc = function
  | Pgm_ptree.Econstant (ConstInt _ as c) ->
      Econstant c, Tyapp (Ty.ts_int, [])
  | Pgm_ptree.Econstant (ConstReal _ as c) ->
      Econstant c, Tyapp (Ty.ts_real, [])
  | Pgm_ptree.Eident (Qident {id=x}) when Mstr.mem x env.dvars ->
      (* local variable *)
      let ty = Mstr.find x env.dvars in
      Elocal x, ty
  | Pgm_ptree.Eident p ->
      let s, tyl, ty = Typing.specialize_fsymbol p env.uc in
      Eglobal s, currying env tyl ty
  | Pgm_ptree.Eapply (e1, e2) ->
      let e1 = expr env e1 in
      let e2 = expr env e2 in
      begin match e1.expr_type with
	| Tyapp (ts, [ty2; ty]) when ts == env.ts_arrow ->
	    expected_type e2 ty2;
	    Eapply (e1, e2), ty
	| _ ->
	    errorm ~loc:e1.expr_loc "this expression is not a function"
      end
  | Pgm_ptree.Elet ({id=x}, e1, e2) ->
      let e1 = expr env e1 in
      let ty1 = e1.expr_type in
      let env = { env with dvars = Mstr.add x ty1 env.dvars } in
      let e2 = expr env e2 in
      Elet (x, e1, e2), e2.expr_type
  | Pgm_ptree.Esequence (e1, e2) ->
      let e1 = expr env e1 in
      expected_type e1 (Tyapp (env.ts_unit, []));
      let e2 = expr env e2 in
      Esequence (e1, e2), e2.expr_type
  | Pgm_ptree.Eskip ->
      Eskip, Tyapp (env.ts_unit, [])
  | Pgm_ptree.Elabel (l, e1) ->
      (* TODO: add label to env *)
      let e1 = expr env e1 in
      Elabel (l, e1), e1.expr_type
  | Pgm_ptree.Eif (e1, e2, e3) ->
      let e1 = expr env e1 in
      expected_type e1 (Tyapp (env.ts_bool, []));
      let e2 = expr env e2 in
      let e3 = expr env e3 in
      expected_type e3 e2.expr_type;
      Eif (e1, e2, e3), e2.expr_type
  | Pgm_ptree.Eassert (k, le) ->
      Eassert (k, le), Tyapp (env.ts_unit, [])
  | Pgm_ptree.Eghost e1 ->
      let e1 = expr env e1 in
      Eghost e1, e1.expr_type
  | Pgm_ptree.Ewhile (e1, a, e2) ->
      let e1 = expr env e1 in
      expected_type e1 (Tyapp (env.ts_bool, []));
      let e2 = expr env e2 in
      expected_type e1 (Tyapp (env.ts_unit, []));
      Ewhile (e1, a, e2), Tyapp (env.ts_unit, [])
  | Pgm_ptree.Elazy (op, e1, e2) ->
      let e1 = expr env e1 in
      expected_type e1 (Tyapp (env.ts_bool, []));
      let e2 = expr env e2 in
      expected_type e2 (Tyapp (env.ts_bool, []));
      Elazy (op, e1, e2), Tyapp (env.ts_bool, [])

let code uc id e =
  let env = create_denv uc in
  ignore (expr env e)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
