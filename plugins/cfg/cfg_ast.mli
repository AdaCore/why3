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

type label = Ptree.ident

type loop_clause = Invariant | Variant

type cfg_instr = {
    cfg_instr_desc : cfg_instr_desc;
    cfg_instr_loc  : Loc.position;
  }

and cfg_term = {
    cfg_term_desc : cfg_term_desc;
    cfg_term_loc : Loc.position;
  }

and cfg_instr_desc =
  | CFGinvariant of (loop_clause * ident option * Ptree.term * int option ref) list
  (** possibly named invariants *)
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
  { cf_name: ident;
    cf_args: Ptree.binder list;
    cf_retty: Ptree.pty;
    cf_mask: Ity.mask;
    cf_pat: Ptree.pattern;
    cf_spec: Ptree.spec;
    cf_attrs: Ptree.attr list;
    cf_locals: (bool * ident * Ptree.pty * Ptree.expr option) list;
    cf_block0: block;
    cf_blocks: (label * block) list;
  }

type cfg_decl =
  | Dmlw_decl of Ptree.decl
  | Dletcfg of cfg_fundef
  | Dreccfg of cfg_fundef list
  | Dscope of Loc.position * bool * ident * cfg_decl list

type cfg_file = (ident * cfg_decl list) list
  (** a list of modules containing lists of declarations *)
