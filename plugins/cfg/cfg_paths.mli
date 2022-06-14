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

open Why3
open Ptree

val debug : Debug.flag

val translate_cfg_fundef :
  ident * 'a * pty * pattern *  Ity.mask * spec *
      (ghost * ident * pty) list *
        Cfg_ast.block * (Cfg_ast.label * Cfg_ast.block) list ->
  ident * bool * Expr.rs_kind * 'a *  pty option * pattern *
    Ity.mask * spec * expr

val translate_letcfg :
  ident * binder list * pty * pattern * Ity.mask * spec *
    (ghost * ident * pty) list * Cfg_ast.block *
      (Cfg_ast.label * Cfg_ast.block) list ->
  decl

val translate_reccfg :
  (ident * binder list * pty * pattern * Ity.mask * spec *
     (ghost * ident * pty) list *
       Cfg_ast.block * (Cfg_ast.label * Cfg_ast.block) list)
    list -> decl
