(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Why3
open Ident
open Denv
open Ty
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_module
open Mlw_dty

type loc = Loc.position

type ident = Ptree.ident

type constant = Term.constant

type assertion_kind = Ptree.assertion_kind

type lazy_op = Ptree.lazy_op

type for_direction = Ptree.for_direction

(*****************************************************************************)
(* phase 1: introduction of destructive types *)

(* user type_v *)

type ghost = bool
type dpre = Ptree.pre
type dpost_fmla = Ptree.lexpr
type dexn_post_fmla = Ptree.lexpr
type dpost = dpost_fmla * (Term.lsymbol * dexn_post_fmla) list

type dueffect = {
  du_reads  : Ptree.lexpr list;
  du_writes : Ptree.lexpr list;
  du_raises : xsymbol list;
}

type dubinder = ident * ghost * dity

(**
type dutype_v =
  | DUTpure  of Denv.dty
  | DUTarrow of dubinder list * dutype_c

and dutype_c =
  { duc_result_type : dutype_v;
    duc_effect      : dueffect;
    duc_pre         : Ptree.lexpr;
    duc_post        : Ptree.lexpr * (Term.lsymbol * Ptree.lexpr) list; }
**)

type dvariant = Ptree.lexpr * Term.lsymbol option

type dloop_annotation = {
  dloop_invariant : Ptree.lexpr option;
  dloop_variant   : dvariant option;
}

type dexpr = {
  dexpr_desc : dexpr_desc;
  dexpr_type : dity;
  dexpr_lab  : Ident.label list;
  dexpr_loc  : loc;
}

and dexpr_desc =
  | DEconstant of constant
  | DElocal of string
  | DEglobal_pv of pvsymbol
  | DEglobal_ps of psymbol
  | DEglobal_pl of plsymbol * dexpr list
  | DElogic of Term.lsymbol * dexpr list
  | DEapply of dexpr * dexpr
  | DEfun of dubinder list * dtriple
  | DElet of ident * dexpr * dexpr
  | DEletrec of drecfun list * dexpr
  | DEassign of dexpr * Term.lsymbol * int * dexpr
  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEloop of dloop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEmatch of dexpr * (Denv.dpattern * dexpr) list
  | DEabsurd
  | DEraise of xsymbol * dexpr option
  | DEtry of dexpr * (xsymbol * string option * dexpr) list
  | DEfor of ident * dexpr * for_direction * dexpr * Ptree.lexpr option * dexpr
  | DEassert of assertion_kind * Ptree.lexpr
  | DEmark of string * dexpr
  (* | DEany of dutype_c *)

and drecfun = (ident * Denv.dty) * dubinder list * dvariant option * dtriple

and dtriple = dpre * dexpr * dpost
