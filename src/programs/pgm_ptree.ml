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

type ident = Ptree.ident

type qualid = Ptree.qualid

type constant = Term.constant

type assertion_kind = Aassert | Aassume | Acheck

type lazy_op = LazyAnd | LazyOr

type logic = Lexing.position * string

type lexpr = logic

type variant = lexpr * qualid

type loop_annotation = {
  loop_invariant : lexpr option;
  loop_variant   : variant option;
}

type effect = {
  pe_reads  : ident list;
  pe_writes : ident list;
  pe_raises : ident list;
}

type pre = lexpr

type post = lexpr * (ident * lexpr) list

type type_v =
  | Tpure of Ptree.pty
  | Tarrow of binder list * type_c

and type_c =
  { pc_result_name : ident;
    pc_result_type : type_v;
    pc_effect      : effect;
    pc_pre         : pre;
    pc_post        : post; }

and binder = ident * type_v option

type expr = {
  expr_desc : expr_desc;
  expr_loc  : loc;
}

and expr_desc =
  (* lambda-calculus *)
  | Econstant of constant
  | Eident of qualid
  | Eapply of expr * expr
  | Efun of binder list * triple
  | Elet of ident * expr * expr
  | Eletrec of (ident * binder list * variant option * triple) list * expr
  (* control *)
  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Ewhile of expr * loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Ematch of expr list * (Ptree.pattern list * expr) list
  | Eskip 
  | Eabsurd
  | Eraise of ident * expr option
  | Etry of expr * (ident * ident option * expr) list
  (* annotations *)
  | Eassert of assertion_kind * lexpr
  | Eghost of expr
  | Elabel of ident * expr
  | Ecast of expr * Ptree.pty
  | Eany of type_c

  (* TODO: ghost *)

and triple = pre * expr * post

type decl =
  | Dlet    of ident * expr
  | Dletrec of (ident * binder list * variant option * triple) list
  | Dlogic  of logic
  | Dparam  of ident * type_v
  | Dexn    of ident * Ptree.pty option

type file = decl list

