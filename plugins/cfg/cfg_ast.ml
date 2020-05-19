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

type pty = Ptree.pty

type ident = Ptree.ident

type binder = Ptree.binder

type pattern = Ptree.pattern

type spec = Ptree.spec

type label = Ptree.ident

(*
type cfg_expr = {
    cfg_expr_desc : cfg_expr_desc;
    cfg_expr_loc  : Loc.position;
  }

and cfg_expr_desc =
  | CFGtrue
  (** Boolean literal [True] *)
  | CFGfalse
  (** Boolean literal [False] *)
  | CFGconst of Constant.constant
  (** Constant literals *)
  (* TODO: expand -> variables, bin op, function call... or any Ptree.expr ! *)
 *)

type cfg_instr = {
    cfg_instr_desc : cfg_instr_desc;
    cfg_instr_loc  : Loc.position;
  }

and cfg_instr_desc =
  | CFGgoto of label
(** goto a label "goto L" *)
  | CFGswitch of Ptree.expr * switch_branch list
(** pattern-matching *)
  | CFGexpr of Ptree.expr
(*
  | CFGassign of ident * cfg_expr
  (** assignment "x <- e" *)
  | CFGassert of Expr.assertion_kind * Ptree.term
  (** assert or assume or check *)
  (* TODO: expand -> branching, procedure call... or any Ptree.expr ! *)
*)

and switch_branch = Ptree.pattern * block
(** pattern -> regular WhyML expression ; goto ident *)

and block = cfg_instr list


type cfg_fundef =
  ident * binder list * pty * pattern * spec * binder list * block * (label * block) list
(** function name, argument, return type, ?, contract,
    local variables, first block, other blocks *)

type cfg_decl =
  | Dmlw_decl of Ptree.decl
  | Dletcfg of cfg_fundef list

type cfg_file = (ident * cfg_decl list) list
  (** a list of modules containing lists of declarations *)
