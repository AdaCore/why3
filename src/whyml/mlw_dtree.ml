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

(* user type_v *)

type ghost = bool
type dpre = Ptree.pre
type dpost = Ptree.pre
type dxpost = (xsymbol * dpost) list
type dbinder = ident * ghost * dity

(**
type dutype_v =
  | DUTpure  of Denv.dty
  | DUTarrow of dbinder list * dutype_c

and dutype_c =
  { duc_result_type : dutype_v;
    duc_effect      : deffect;
    duc_pre         : Ptree.lexpr;
    duc_post        : Ptree.lexpr * (Term.lsymbol * Ptree.lexpr) list; }
**)

type dvariant = Ptree.lexpr * Term.lsymbol option

type dinvariant = Ptree.lexpr option

type dexpr = {
  dexpr_desc : dexpr_desc;
  dexpr_type : dity;
  dexpr_lab  : Ident.label list;
  dexpr_loc  : loc;
}

and dexpr_desc =
  | DEconstant of Term.constant
  | DElocal of string
  | DEglobal_pv of pvsymbol
  | DEglobal_ps of psymbol
  | DEglobal_pl of plsymbol
  | DEglobal_ls of Term.lsymbol
  | DEapply of dexpr * dexpr list
  | DEfun of dlambda
  | DElet of ident * dexpr * dexpr
  | DEletrec of drecfun list * dexpr
  | DEassign of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEloop of dvariant list * dinvariant * dexpr
  | DElazy of Ptree.lazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEmatch of dexpr * (pre_ppattern * dexpr) list
  | DEabsurd
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * ident * dexpr) list
  | DEfor of ident * dexpr * Ptree.for_direction * dexpr * dinvariant * dexpr
  | DEassert of Ptree.assertion_kind * Ptree.lexpr
  | DEmark of ident * dexpr
  | DEghost of dexpr
(*
  | DEany of deffect
*)

and drecfun = ident * dity * dlambda

and dlambda = dbinder list * dvariant list * dpre * dexpr * dpost * dxpost

(*
and deffect = {
  deff_reads  : dexpr list;
  deff_writes : dexpr list;
  deff_raises : (ghost * xsymbol) list;
}
*)
