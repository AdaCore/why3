(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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

type typ = Ptree.pty

type is_function = bool

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
  | Econd of expr * expr * expr (* e1 if e2 else e3 *)
  | Eunop of unop * expr
  | Ecall of ident * expr list
  | Edot of expr * ident * expr list
  | Elist of expr list   (* [e1, e2, ..., en] *)
  | Etuple of expr list   (* e1, e2, ..., en *)
  | Emake of expr * expr (* [e1] * e2 *)
  | Eget of expr * expr  (* e1[e2] *)

and stmt = {
  stmt_desc: stmt_desc;
  stmt_loc : Loc.position;
}

and stmt_desc =
  | Sblock of block
  | Sif of expr * block * block
  | Sreturn of expr
  | Spass of typ option * Ptree.spec
  | Sassign of expr * expr
  | Swhile of expr * Ptree.invariant * Ptree.variant * block
  | Sfor of ident * expr * Ptree.invariant * block
  | Seval of expr
  | Sset of expr * expr * expr (* e1[e2] = e3 *)
  | Sassert of Expr.assertion_kind * Ptree.term
  | Scall_lemma of ident * Ptree.term list
  | Sbreak
  | Scontinue
  | Slabel of ident

and block = decl list

and decl =
  | Dimport of ident * ident list
  | Ddef of ident * (ident * typ option) list * typ option * Ptree.spec
             * block * is_function
  | Dconst of ident * expr
  | Dstmt of stmt
  | Dlogic of ident * (ident * typ) list * typ option * Ptree.term option
              * Ptree.term option
  | Dprop of Decl.prop_kind * ident * Ptree.term

type file = block
