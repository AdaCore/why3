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

(* intermediate trees for weakest preconditions *)

type loc = Loc.position

type assertion_kind = Pgm_ptree.assertion_kind

type lazy_op = Pgm_ptree.lazy_op

type variant = Pgm_ttree.variant

type reference = Pgm_ttree.reference

type effect = Pgm_ttree.effect

type pre = Pgm_ttree.pre

type post = Pgm_ttree.post

type type_v = Pgm_ttree.type_v
type type_c = Pgm_ttree.type_c
type binder = Pgm_ttree.binder

type loop_annotation = Pgm_ttree.loop_annotation

type expr = {
  expr_desc  : expr_desc;
  expr_type  : Ty.ty;
  expr_effect: Pgm_effect.t;
  expr_loc   : loc;
}

and expr_desc =
  | Elogic of Term.term
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
  | Etry of expr * (Term.lsymbol * Term.vsymbol option * expr) list

  | Eassert of assertion_kind * Term.fmla
  | Eghost of expr
  | Elabel of string * expr
  | Eany of type_c

and recfun = Term.vsymbol * binder list * variant option * triple

and triple = pre * expr * post

type decl =
  | Dlet    of Term.lsymbol * expr
  | Dletrec of (Term.lsymbol * recfun) list
  | Dparam  of Term.lsymbol * type_v

type file = decl list
