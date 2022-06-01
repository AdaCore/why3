(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Cfg_ast
open Why3

val set_stackify :
  (cfg_fundef ->
   (Cfg_ast.ident * bool * Expr.rs_kind * Ptree.binder list *
      Ptree.pty option * Ptree.pattern * Ity.mask *
        Ptree.spec * Ptree.expr))
  -> unit
