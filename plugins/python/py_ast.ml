(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

type ident = Ptree.ident

type unop =
  | Uneg (* -e *)
  | Unot (* not e *)

type binop =
  | Badd | Bsub | Bmul | Bdiv | Bmod    (* + - * / % *)
  | Beq | Bneq | Blt | Ble | Bgt | Bge  (* == != < <= > >= *)
  | Band | Bor                          (* && || *)

type expr = {
  expr_desc: expr_desc;
  expr_loc : Loc.position;
}

and expr_desc =
  | Enone
  | Ebool of bool
  | Eint of string
  | Estring of string
  | Eident of ident
  | Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Ecall of ident * expr list
  | Elist of expr list   (* [e1, e2, ..., en] *)
  | Emake of expr * expr (* [e1] * e2 *)
  | Eget of expr * expr  (* e1[e2] *)

and stmt = {
  stmt_desc: stmt_desc;
  stmt_loc : Loc.position;
}

and stmt_desc =
  | Sif of expr * block * block
  | Sreturn of expr
  | Sassign of ident * expr
  | Swhile of expr * Ptree.invariant * Ptree.variant * block
  | Sfor of ident * expr * Ptree.invariant * block
  | Seval of expr
  | Sset of expr * expr * expr (* e1[e2] = e3 *)
  | Sassert of Expr.assertion_kind * Ptree.term
  | Sbreak
  | Slabel of ident

and block = decl list

and decl =
  | Dimport of ident * ident list
  | Ddef  of ident * ident list * Ptree.spec * block
  | Dstmt of stmt
  | Dlogic of bool (*is_func*) * ident * ident list

type file = block


