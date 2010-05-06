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

type dreference = 
  | DRlocal  of string
  | DRglobal of Term.lsymbol

type deffect = {
  de_reads  : dreference list;
  de_writes : dreference list;
  de_raises : Term.lsymbol list;
}

type dlexpr = Typing.denv * Ptree.lexpr

type dtype_v = 
  | DTpure of Denv.dty
  | DTarrow of dbinder list * dtype_c

and dtype_c = 
  { dc_result_name : string;
    dc_result_type : dtype_v;
    dc_effect      : deffect;
    dc_pre         : dlexpr;
    dc_post        : dlexpr; }

and dbinder = string * dtype_v

type dvariant = Pgm_ptree.lexpr 

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
  | DEletrec of 
      ((string * Denv.dty) * dbinder list * dvariant option * dtriple) list * 
      dexpr

  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEwhile of dexpr *  Pgm_ptree.loop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEmatch of dexpr list * (Typing.dpattern list * dexpr) list
  | DEskip
  | DEabsurd 
  | DEraise of Term.lsymbol * dexpr option

  | DEassert of assertion_kind * Ptree.lexpr
  | DEghost of dexpr
  | DElabel of string * dexpr

and dtriple = dlexpr * dexpr * dlexpr

(* phase 2: typing annotations *)

type variant = Term.term

type reference = 
  | Rlocal  of Term.vsymbol
  | Rglobal of Term.lsymbol

type effect = {
  e_reads  : reference list;
  e_writes : reference list;
  e_raises : Term.lsymbol list;
}

type type_v = 
  | Tpure of Ty.ty
  | Tarrow of binder list * type_c

and type_c = 
  { c_result_name : Term.vsymbol;
    c_result_type : type_v;
    c_effect      : effect;
    c_pre         : Term.fmla;
    c_post        : Term.fmla; }

and binder = Term.vsymbol * type_v

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
  | Eletrec of recfun list * expr

  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Ewhile of expr * loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Ematch of expr list * (Term.pattern list * expr) list
  | Eskip 
  | Eabsurd
  | Eraise of Term.lsymbol * expr option

  | Eassert of assertion_kind * Term.fmla
  | Eghost of expr
  | Elabel of string * expr

and recfun = Term.vsymbol * binder list * variant option * triple

and triple = Term.fmla * expr * Term.fmla

type decl =
  | Dlet    of Term.lsymbol * expr
  | Dletrec of (Term.lsymbol * recfun) list
  | Dparam  of Term.lsymbol * type_v

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
