(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
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
  | Unot (* !e *)

type binop =
  | Badd | Bsub | Bmul | Bdiv | Bmod    (* + - * / % *)
  | Beq | Bneq | Blt | Ble | Bgt | Bge  (* == != < <= > >= *)
  | Band | Bor                          (* && || *)

type ty =
  | Tint

type expr = {
  expr_desc: expr_desc;
  expr_loc : Loc.position;
}

and expr_desc =
  | Eint of string
  | Estring of string
  | Eaddr of ident
  | Eident of ident
  | Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Ecall of ident * expr list
  | Eget of expr * expr  (* e1[e2] *)

and stmt = {
  stmt_desc: stmt_desc;
  stmt_loc : Loc.position;
}

and stmt_desc =
  | Sskip
  | Sif of expr * block * block
  | Sreturn of expr
  | Svar of ty * ident * expr
  | Sassign of ident * expr
  | Swhile of expr * Ptree.invariant * Ptree.variant * block
  | Sfor of stmt * expr * stmt * Ptree.invariant * block
  | Seval of expr
  | Sset of expr * expr * expr (* e1[e2] = e3 *)
  | Sassert of Expr.assertion_kind * Ptree.term
  | Sbreak
  | Slabel of ident

and block = stmt list

type param =
  ty * ident

type decl =
  | Dinclude of ident
  | Dfun     of ty * ident * param list * Ptree.spec * block
  | Dlogic   of bool (*is_func*) * ident * ident list

type file = decl list
