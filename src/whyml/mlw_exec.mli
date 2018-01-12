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

(** Decide whether an expression/symbol/declaration is executable *)

type t
  (** The context in which we make such a decision *)

val create: Mlw_driver.driver -> Decl.known_map -> Mlw_decl.known_map -> t

val is_exec_term: t -> Term.term -> bool
val is_exec_lsymbol: t -> Term.lsymbol -> bool
val is_exec_decl: t -> Decl.decl -> bool

val is_exec_expr: t -> Mlw_expr.expr -> bool
val is_exec_pdecl: t -> Mlw_decl.pdecl -> bool

