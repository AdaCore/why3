(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Mlw_ty
open Mlw_expr
open Mlw_dty

type loc = Loc.position
type ident = Ptree.ident

type ghost = bool

type dpre = Ptree.lexpr list
type dpost = (Ptree.pattern * Ptree.lexpr) list
type dxpost = dpost Mexn.t
type deffect = Ptree.lexpr list
type dvariant = Ptree.lexpr * Term.lsymbol option
type dinvariant = Ptree.lexpr list

type dspec = {
  ds_pre     : dpre;
  ds_post    : dpost;
  ds_xpost   : dxpost;
  ds_reads   : deffect;
  ds_writes  : deffect;
  ds_variant : dvariant list;
}

type dbinder = ident * ghost * dity

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec

type dexpr = {
  de_desc : dexpr_desc;
  de_type : dvty;
  de_lab  : Ident.Slab.t;
  de_loc  : loc;
}

and dexpr_desc =
  | DEconstant of Number.constant
  | DElocal of string
  | DEglobal_pv of pvsymbol
  | DEglobal_ps of psymbol
  | DEglobal_pl of plsymbol
  | DEglobal_ls of Term.lsymbol
  | DEapply of dexpr * dexpr list
  | DEfun of dbinder list * dtriple
  | DElet of ident * ghost * dexpr * dexpr
  | DEletrec of drecfun list * dexpr
  | DEassign of plsymbol * dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEloop of dvariant list * dinvariant * dexpr
  | DElazy of Ptree.lazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEmatch of dexpr * (pre_ppattern * dexpr) list
  | DEabsurd
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * pre_ppattern * dexpr) list
  | DEfor of ident * dexpr * Ptree.for_direction * dexpr * dinvariant * dexpr
  | DEassert of Ptree.assertion_kind * Ptree.lexpr
  | DEabstract of dtriple
  | DEmark of ident * dexpr
  | DEghost of dexpr
  | DEany of dtype_c

and drecfun = ident * ghost * dvty * dbinder list * dtriple
and dtriple = dexpr * dspec
