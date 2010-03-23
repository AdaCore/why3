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
  uc : theory_uc; (* the theory under construction *)
  utyvars : (string, type_var) Hashtbl.t; (* user type variables *)
  dvars : dty Mstr.t; (* local variables, to be bound later *)
  ts_arrow : Ty.tysymbol;
}

let create_denv uc = {
  uc = uc;
  utyvars = Hashtbl.create 17;
  dvars = Mstr.empty;
  ts_arrow = ns_find_ts (get_namespace uc) ["Prelude"; "arrow"];
}
(*****************************************************************************)

let currying env tyl ty =
  let make_arrow_type ty1 ty2 = Tyapp (env.ts_arrow, [ty1; ty2]) in
  List.fold_right make_arrow_type tyl ty

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
	    if not (Denv.unify ty2 e2.expr_type) then
	      errorm ~loc:e2.expr_loc 
		"this expression has type %a, but is expected to have type %a"
		print_dty e2.expr_type print_dty ty2;
	    Eapply (e1, e2), ty
	| _ ->
	    errorm ~loc:e1.expr_loc "this expression is not a function"
      end
  | _ -> 
      assert false (*TODO*)
(*   | Eident of qualid *)
(*   | Eapply of 'info expr * 'info expr *)
(*   | Esequence of 'info expr * 'info expr *)
(*   | Eif of 'info expr * 'info expr * 'info expr *)
(*   | Eskip  *)
(*   | Eassert of assertion_kind * lexpr *)
(*   | Elazy_and of 'info expr * 'info expr *)
(*   | Elazy_or of 'info expr * 'info expr *)
(*   | Elet of ident * 'info expr * 'info expr *)
(*   | Eghost of 'info expr *)
(*   | Elabel of ident * 'info expr *)
(*   | Ewhile of 'info expr * loop_annotation * 'info expr *)

let code uc id e =
  let env = create_denv uc in
  ignore (expr env e)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
