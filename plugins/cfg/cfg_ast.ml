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
  | CFGlabel of ident * cfg_expr
  (** declare a label *)
  | CFGgoto of ident
  (** goto a label *)
  | CFGassert of Expr.assertion_kind * Ptree.term
(* TODO: expand *)


type cfg_fundef =
  ident * binder list * pty * pattern * spec * binder list * cfg_expr
(** function name, argument, return type, ?, contract, local variables, body *)

type cfg_decl =
  | Dmlw_decl of Ptree.decl
  | Dletcfg of cfg_fundef list

type cfg_file = (ident * cfg_decl list) list
  (** a list of modules containing lists of declarations *)
