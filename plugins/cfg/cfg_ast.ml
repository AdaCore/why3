(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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
  | Tvoid
  | Tint
  | Tarray

type loop_annotation =
  Ptree.invariant * Ptree.variant

type expr = {
  expr_desc: expr_desc;
  expr_loc : Loc.position;
}

and expr_desc =
  | Eunit
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
  | Sif of expr * stmt * stmt
  | Sreturn of expr
  | Svar of ty * ident * expr
  | Sassign of ident * expr
  | Swhile of expr * loop_annotation * stmt
  (* | Sfor of stmt * expr * stmt * loop_annotation * block *)
  | Seval of expr
  | Sset of expr * expr * expr (* e1[e2] = e3 *)
  | Sassert of Expr.assertion_kind * Ptree.term
  | Sbreak
  | Slabel of ident
  | Sblock of stmt list

type param =
  ty * ident

type decl =
  | Dinclude of ident
  | Dfun     of ty * ident * param list * Ptree.spec * stmt
  | Dlogic   of ty option * ident * param list * Ptree.term option
  | Dprop    of Decl.prop_kind * ident * Ptree.term

type file = decl list
