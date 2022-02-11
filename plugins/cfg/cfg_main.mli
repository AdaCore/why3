(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)
open Cfg_ast
open Why3
open Pmodule
open Ptree

val set_stackify :
  (cfg_fundef ->
    (Cfg_ast.ident * bool * Why3.Expr.rs_kind * Why3.Ptree.binder list *
         Why3.Ptree.pty option * Why3.Ptree.pattern * Why3.Ity.mask *
         Why3.Ptree.spec * Why3.Ptree.expr)
  ) -> unit