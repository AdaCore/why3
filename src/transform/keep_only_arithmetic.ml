(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Ty
open Theory
open Ident

type fmla =
  | Unsupported
  | Tautology
  | Contradiction
  | Formula of term

(* Filter all the formulas that are not inequalities or equalities about
   int/reals *)
(* Also performs some simplifications *)
let rec get_fmla symbols f =
  let rec get = get_fmla symbols in
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> (
    match get f1 with
    | Unsupported
    | Tautology ->
      get f2
    | Contradiction -> Contradiction
    | Formula f1 -> (
      match get f2 with
      | Unsupported
      | Tautology ->
        Formula f1
      | Contradiction -> Contradiction
      | Formula f2 -> Formula (t_and f1 f2)))
  | Tbinop (Tor, f1, f2) -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Tautology
    | Contradiction -> get f2
    | Formula f1 -> (
      match get f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula f1
      | Formula f2 -> Formula (t_or f1 f2)))
  | Tbinop (Timplies, f1, f2) -> (
    match get f1 with
    | Unsupported
    | Contradiction ->
      Unsupported
    | Tautology -> get f2
    | Formula f1 -> (
      match get f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula (t_implies f1 t_false)
      | Formula f2 -> Formula (t_implies f1 f2)))
  | Ttrue -> Tautology
  | Tfalse -> Contradiction
  | Tnot f1 -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Contradiction
    | Contradiction -> Tautology
    | Formula f -> Formula (t_not f))
  | Tapp (ls, [ t1; t2 ]) ->
    if ls_equal ls ps_equ then
      match t1.t_ty with
      | Some ty ->
        if ty_equal ty ty_int || ty_equal ty ty_real then
          Formula f
        else
          Unsupported
      | None -> Formula f
    else if List.exists (fun _ls -> ls_equal ls _ls) symbols then
      Formula f
    else
      Unsupported
  | _ -> Unsupported

let filter_non_arith symbols d =
  match d.d_node with
  | Dtype ts when ts_equal ts ts_int || ts_equal ts ts_real -> [ d ]
  | Dparam { ls_args = []; ls_value = Some ty }
    when ty_equal ty ty_int || ty_equal ty ty_real ->
    [ d ]
  | Dprop (Paxiom, pr, f) -> (
    match get_fmla symbols f with
    | Contradiction -> [ create_prop_decl Paxiom pr t_false ]
    | Formula f -> [ create_prop_decl Paxiom pr f ]
    | _ -> [])
  | Dprop (Pgoal, pr, f) -> (
    match get_fmla symbols f with
    | Unsupported
    | Contradiction ->
      [ create_prop_decl Paxiom pr t_true ]
    | Tautology -> [ create_prop_decl Pgoal pr t_false ]
    | Formula f -> [ create_prop_decl Pgoal pr (t_not f) ])
  | _ -> []

let keep_only_arithmetic env =
  let symbol_names =
    [
      Ident.op_infix "<";
      Ident.op_infix "<=";
      Ident.op_infix ">";
      Ident.op_infix ">=";
    ]
  in
  let int = Env.read_theory env [ "int" ] "Int" in
  let int_symbols =
    List.map (fun name -> ns_find_ls int.th_export [ name ]) symbol_names
  in
  let real = Env.read_theory env [ "real" ] "Real" in
  let real_symbols =
    List.map (fun name -> ns_find_ls real.th_export [ name ]) symbol_names
  in
  Trans.decl (filter_non_arith (int_symbols @ real_symbols)) None

let () =
  Trans.register_env_transform "keep_only_arithmetic" keep_only_arithmetic
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
