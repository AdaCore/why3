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

type loc = Loc.position

type constant = Term.constant

type assertion_kind = Pgm_ptree.assertion_kind

type lazy_op = Pgm_ptree.lazy_op

(* phase 1: destructive typing *)

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
  | DElet of string * dexpr * dexpr

  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEwhile of dexpr *  Pgm_ptree.loop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEskip 

  | DEassert of assertion_kind * Ptree.lexpr
  | DEghost of dexpr
  | DElabel of string * dexpr

(* phase 2: typing annotations *)

type loop_annotation = {
  loop_invariant : Term.fmla option;
  loop_variant   : Term.term option;
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
  | Elet of Term.vsymbol * expr * expr

  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Ewhile of expr * loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Eskip 

  | Eassert of assertion_kind * Term.fmla
  | Eghost of expr
  | Elabel of string * expr

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
