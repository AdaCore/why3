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

type fmla =
  | Unsupported
  | Tautology
  | Contradiction
  | Formula of term

(* Filter all the formulas that are not inequalities or equalities *)
(* Also performs some simplifications *)
let rec get_fmla f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported
    | Tautology ->
      get_fmla f2
    | Contradiction -> Contradiction
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported
      | Tautology ->
        Formula f1
      | Contradiction -> Contradiction
      | Formula f2 -> Formula (t_and f1 f2)))
  | Tbinop (Tor, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported -> Unsupported
    | Tautology -> Tautology
    | Contradiction -> get_fmla f2
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula f1
      | Formula f2 -> Formula (t_or f1 f2)))
  | Tbinop (Timplies, f1, f2) -> (
    match get_fmla f1 with
    | Unsupported
    | Contradiction ->
      Unsupported
    | Tautology -> get_fmla f2
    | Formula f1 -> (
      match get_fmla f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula (t_implies f1 t_false)
      | Formula f2 -> Formula (t_implies f1 f2)))
  | Ttrue -> Tautology
  | Tfalse -> Contradiction
  | Tnot f1 -> (
    match get_fmla f1 with
    | Unsupported -> Unsupported
    | Tautology -> Contradiction
    | Contradiction -> Tautology
    | Formula f -> Formula (t_not f))
  | Tapp (ls, [ t1; t2 ]) ->
    if ls_equal ls ps_equ then
      match t1.t_ty with
      | Some ty ->
        if not (Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real) then
          Unsupported
        else
          Formula f
      | None -> Formula f
    else
      Unsupported
  | _ -> Unsupported

let keep_only_arithmetic d =
  match d.d_node with
  | Dparam { ls_args = []; ls_value = Some ty }
    when Ty.ty_equal ty Ty.ty_int || Ty.ty_equal ty Ty.ty_real ->
    [ d ]
  | Dprop (Paxiom, pr, f) -> (
    match get_fmla f with
    | Contradiction -> [ create_prop_decl Paxiom pr t_false ]
    | Formula f -> [ create_prop_decl Paxiom pr f ]
    | _ -> [])
  | Dprop (Pgoal, pr, f) -> (
    match get_fmla f with
    | Unsupported
    | Contradiction ->
      [ create_prop_decl Paxiom pr t_true ]
    | Tautology -> [ create_prop_decl Pgoal pr t_false ]
    | Formula f -> [ create_prop_decl Pgoal pr (t_not f) ])
  | _ -> []

let () =
  Trans.register_transform "keep_only_arithmetic"
    (Trans.decl keep_only_arithmetic None)
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
