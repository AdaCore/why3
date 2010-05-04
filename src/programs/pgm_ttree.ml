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

open Why

type loc = Loc.position

type constant = Term.constant

type assertion_kind = Pgm_ptree.assertion_kind

type lazy_op = Pgm_ptree.lazy_op

(* phase 1: destructive typing *)

type deffect = string list

type dtype_v = 
  | DTpure of Denv.dty
  | DTarrow of (string * dtype_v) list * dtype_c

and dtype_c = 
  { dc_result_name : Term.vsymbol;
    dc_result_type : dtype_v;
    dc_effect      : deffect;
    dc_pre         : Ptree.lexpr;
    dc_post        : Ptree.lexpr; }

type dvariant = Pgm_ptree.lexpr 

type dbinder = string * dtype_v

type dlexpr = Typing.denv * Ptree.lexpr

type dexpr = {
  dexpr_desc : dexpr_desc;
  dexpr_denv : Typing.denv;
  dexpr_type : Denv.dty;
  dexpr_loc  : loc;
}

and dexpr_desc =
  | DEconstant of constant
  | DElocal of string
  | DEglobal of Term.lsymbol
  | DEapply of dexpr * dexpr
  | DEfun of dbinder list * dtriple
  | DElet of string * dexpr * dexpr
  | DEletrec of (string * dbinder list * dvariant option * dtriple) * dexpr

  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEwhile of dexpr *  Pgm_ptree.loop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEskip
  | DEabsurd 

  | DEassert of assertion_kind * Ptree.lexpr
  | DEghost of dexpr
  | DElabel of string * dexpr

and dtriple = dlexpr * dexpr * dlexpr

(* phase 2: typing annotations *)

type variant = Term.term

type effect = Term.vsymbol list

type type_v = 
  | Tpure of Ty.ty
  | Tarrow of Term.vsymbol list * type_c

and type_c = 
  { pc_result_name : Term.vsymbol;
    pc_result_type : type_v;
    pc_effect      : effect;
    pc_pre         : Term.fmla;
    pc_post        : Term.fmla; }

type binder = Term.vsymbol * type_v

type loop_annotation = {
  loop_invariant : Term.fmla option;
  loop_variant   : variant option;
}

type expr = {
  expr_desc : expr_desc;
  expr_type : Ty.ty;
  expr_loc  : loc;
}

and expr_desc =
  | Econstant of constant
  | Elocal of Term.vsymbol
  | Eglobal of Term.lsymbol
  | Eapply of expr * expr
  | Efun of binder list * triple
  | Elet of Term.vsymbol * expr * expr

  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Ewhile of expr * loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Eskip 
  | Eabsurd

  | Eassert of assertion_kind * Term.fmla
  | Eghost of expr
  | Elabel of string * expr

and triple = Term.fmla * expr * Term.fmla

type decl =
  | Dlet of Term.lsymbol * expr
  | Dletrec of (Term.lsymbol * Term.vsymbol list * variant option * triple) list

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
