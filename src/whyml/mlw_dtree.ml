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
open Mlw_ty
open Mlw_expr
open Mlw_dty

type loc = Loc.position
type ident = Ptree.ident

type ghost = bool

type dpre = Ptree.pre
type dpost = Ptree.pre
type dxpost = dpost Mexn.t
type dvariant = Ptree.lexpr * Term.lsymbol option
type dinvariant = Ptree.lexpr option

type deffect = {
  deff_reads  : Ptree.lexpr list;
  deff_writes : Ptree.lexpr list;
  deff_raises : xsymbol list;
}

type dspec = {
  ds_pre     : dpre;
  ds_post    : dpost;
  ds_xpost   : dxpost;
  ds_effect  : deffect;
  ds_variant : dvariant list;
}

type dbinder = ident * ghost * dity

type dtype_v =
  | DSpecV of ghost * dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec

type dexpr = {
  de_desc : dexpr_desc;
  de_type : dvty;
  de_lab  : Ident.Slab.t;
  de_loc  : loc;
}

and dexpr_desc =
  | DEconstant of Term.constant
  | DElocal of string
  | DEglobal_pv of pvsymbol
  | DEglobal_ps of psymbol
  | DEglobal_pl of plsymbol
  | DEglobal_ls of Term.lsymbol
  | DEapply of dexpr * dexpr list
  | DEfun of dbinder list * dtriple
  | DElet of ident * ghost * dexpr * dexpr
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
  | DEabstract of dtriple
  | DEmark of ident * dexpr
  | DEghost of dexpr
  | DEany of dtype_c

and drecfun = ident * ghost * dvty * dbinder list * dtriple
and dtriple = dexpr * dspec
