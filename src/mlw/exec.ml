(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Decide wheter an expression/symbol/declaration is executable *)

(* Based on the implementation by Jacques-Pascal Deplaix (2014), *)
(* for the old system *)

open Ident
open Pdecl
open Ity
open Expr
open Term
open Pdriver

type t = {
    driver       : Pdriver.driver;
    th_known_map : Decl.known_map;
    mo_known_map : Pdecl.known_map;
    is_exec_id   : bool Hid.t;
}

let create dr thkm mokm =
  { driver = dr;
    th_known_map = thkm;
    mo_known_map = mokm;
    is_exec_id = Hid.create 16; }

let has_syntax {driver = drv} id =
  Mid.mem id (drv.drv_syntax) || Mid.mem id (drv.drv_converter)

let is_exec_pdecl _ _ = assert false (* TODO *)
(*
let rec is_exec_expr cxt e =
  match e.e_node with
  | Evar _
  | Econst _
  | Eassert _
  | Eabsurd -> true
  | Econst  of Number.constant
  | Eexec   of cexp * cty
  | Eassign of assign list
  | Elet    of let_defn * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (prog_pattern * expr) list
  | Ewhile  of expr * invariant list * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant list * expr
  | Etry    of expr * (pvsymbol list * expr) Mexn.t
  | Eraise  of xsymbol * expr
  | Eassert of assertion_kind * term
  | Eghost  of expr
  | Epure   of term
  | Eabsurd

let is_exec_pdecl cxt pd =
  match pd.pd_node with
  | PDtype _ | PDexn  _ -> true
  | PDpure -> false
  | PDlet (LDvar (pv, _)) when pv.pv_ghost -> false
  | PDlet (LDsym (_, c)) when cty_ghost c.c_cty -> false
  | PDlet (LDvar ({pv_vs = vs}, _)) ->
     has_syntax cxt vs.vs_name
  | PDlet (LDsym ({rs_name = rs}, {c_node = Cfun e})) ->
     is_exec_expr cxt e
  | _ -> assert false
*)
