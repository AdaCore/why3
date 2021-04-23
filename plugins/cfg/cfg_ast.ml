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

open Why3

type ident = Ptree.ident

type label = Ptree.ident

type cfg_instr = {
    cfg_instr_desc : cfg_instr_desc;
    cfg_instr_loc  : Loc.position;
  }
and cfg_term = {
    cfg_term_desc : cfg_term_desc;
    cfg_term_loc : Loc.position;
  }
and cfg_instr_desc =
  | CFGinvariant of (ident * Ptree.term) list
  (** named invariants *)
  | CFGexpr of Ptree.expr
  (** any other regular WhyML expressions *)
and cfg_term_desc =
  | CFGgoto of label
  (** goto a label "goto L" *)
  | CFGswitch of Ptree.expr * switch_branch list
  (** pattern-matching *)
  | CFGreturn of Ptree.expr
  (** return from a cfg *)
  | CFGabsurd
  (** unreachable *)
and switch_branch = Ptree.pattern * cfg_term
(** pattern -> regular WhyML expression ; goto ident *)

and block = (cfg_instr list * cfg_term)

type cfg_fundef =
  ident * Ptree.binder list * Ptree.pty * Ptree.pattern * Ity.mask * Ptree.spec *
    (bool * ident * Ptree.pty) list * block * (label * block) list
(** function name, argument, return type, ?, contract,
    (ghost) local variables, first block, other blocks *)

type cfg_decl =
  | Dmlw_decl of Ptree.decl
  | Dletcfg of cfg_fundef
  | Dreccfg of cfg_fundef list
  | Dscope of Loc.position * bool * ident * cfg_decl list

type cfg_file = (ident * cfg_decl list) list
  (** a list of modules containing lists of declarations *)
