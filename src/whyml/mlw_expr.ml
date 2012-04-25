(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why3
open Ident
open Ty
open Term
open Mlw_ty

(** program variables *)

type pvsymbol = {
  pv_vs   : vsymbol; (* has a dummy type if pv_vty is an arrow *)
  pv_vty  : vty;
  pv_tvs  : Stv.t;
  pv_regs : Sreg.t;
}

module Pv = Util.StructMake (struct
  type t = pvsymbol
  let tag pv = Hashweak.tag_hash pv.pv_vs.vs_name.id_tag
end)

module Spv = Pv.S
module Mpv = Pv.M

let pv_equal : pvsymbol -> pvsymbol -> bool = (==)

let ts_dummy = create_tysymbol (id_fresh "arrow_dummy") [] None
let ty_dummy = ty_app ts_dummy []

let create_pvsymbol id vtv =
  let ty = ty_of_ity vtv.vtv_ity in
  let vs = create_vsymbol id ty in
  { pv_vs      = vs;
    pv_vty     = VTvalue vtv;
    pv_tvs     = vtv.vtv_tvs;
    pv_regs    = vtv.vtv_regs;
  }

exception NotValue of pvsymbol

let vtv_of_pv pv = match pv.pv_vty with
  | VTvalue vtv -> vtv
  | VTarrow _ -> raise (NotValue pv)

(** program symbols *)

type psymbol = {
  ps_name : ident;
  ps_vty  : vty_arrow;
  ps_tvs  : Stv.t;
  ps_regs : Sreg.t;
  (* these sets cover the type variables and regions of the defining
     lambda that cannot be instantiated. Every other type variable
     and region in ps_vty is generalized and can be instantiated. *)
}

let ps_equal : psymbol -> psymbol -> bool = (==)

(** program/logic symbols *)

type plsymbol = {
  pl_ls     : lsymbol;
  pl_args   : vty_value list;
  pl_value  : vty_value;
  pl_effect : effect;
}

let pl_equal : plsymbol -> plsymbol -> bool = (==)

let create_plsymbol id args value =
  let ty_of_vtv vtv = ty_of_ity vtv.vtv_ity in
  let pure_args = List.map ty_of_vtv args in
  let ls = create_fsymbol id pure_args (ty_of_vtv value) in
  let effect = Util.option_fold eff_read eff_empty value.vtv_mut in
  let arg_reset acc a = Util.option_fold eff_reset acc a.vtv_mut in
  let effect = List.fold_left arg_reset effect args in {
    pl_ls     = ls;
    pl_args   = args;
    pl_value  = value;
    pl_effect = effect;
  }

(* TODO: patterns *)

(* program expressions *)

type pre   = term (* precondition *)
type post  = term (* postcondition *)
type xpost = (vsymbol * post) Mexn.t (* exceptional postconditions *)

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_tvs    : Stv.t Mid.t;
  e_regs   : Sreg.t Mid.t;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Elogic  of term
  | Esymb   of pvsymbol
  | Ecast   of psymbol * ity_subst
  | Eapp    of pvsymbol * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of pvsymbol * expr * expr
  | Eassign of pvsymbol * pvsymbol (* mutable pv <- expr *)
  | Eany

and let_defn = {
  ld_pv   : pvsymbol;
  ld_expr : expr;
}

and rec_defn = {
  rd_ps     : psymbol;
  rd_lambda : lambda;
}

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : pre;
  l_expr    : expr;
  l_post    : post;
  l_xpost   : xpost;
}

(*
  - A "proper type" of a vty [v] is [v] with empty specification
    (effect/pre/post/xpost). Basically, it is formed from pv_ity's
    of pvsymbols in the arguments and the result of [v].

  - Given a vty [v], [vty_freevars v] and [vty_topregions v] return
    the sets of type variables and regions, respectively, that occur
    in the proper type of [v]. We will call them "proper" type vars
    and regions of [v].

  - The specification (effect/pre/post/xpost) of a vty [v] may contain
    type vars and regions that do not occur in the proper type of [v].
    We will call them "extra" type vars and regions of [v].

  - An expression [e] provides the maps [e.e_tvs] and [e.e_regs] from
    idents (vsymbols, pvsymbols, psymbols, ppsymbols) occurring in [e]
    (including asserts, variant, pre- and post-conditions) to sets of
    type vars and regions, respectively, that are "associated" to
    those idents.

  - Every type var in [vs.vs_ty] is associated to [vs].

  - Every type var and region in [pv.pv_ity] is associated to [pv].

  - A psymbol (monomorphic program symbol) [p] provides the sets [p.p_tvs]
    and [p.p_regs] of its associated type vars and regions, respectively.
    These are exactly the unions of the proper type vars and regions of
    [p.p_vty] with the type vars and regions in the range of [e.e_tvs]
    and [e.e_regs], where [e] is the defining expression of [p].

  - A ppsymbol (polymorphic program symbol) [pp] provides the sets
    [pp.pp_tvs] and [pp.pp_regs] of its associated type vars and regions.
    Given a mutually recursive definition
      let rec pp1 pv11 pv12 = expr1 { spec1 }
      with    pp2 pv21 pv22 = expr2 { spec2 }
    we compute the associated type vars of [pp1] as follows:
      1. we combine [expr1.e_tvs] with the corresponding map of [spec1]
      2. we remove from the resulting map the idents of [pv11] and [pv12]
      3. we remove from the resulting map the idents of [pp1] and [pp2]
      4. [pp1.pp_tvs] is the union of the range of the resulting map
    Region sets are computed in the same way. (Don't forget to refresh
    [expr1] and [expr2] if the sets of [pp1] and [pp2] have changed.)

  - Every proper type var and region of [pp.pp_vty] that is not associated
    to [pp] is generalized. Every extra type var and region of [pp.pp_vty]
    must be associated to [pp] <*> and is not generalized. A substitution
    given to [vty_full_inst] must instantiate every type var and region in
    [pp.pp_tvs] and [pp.pp_regs] to itself.

    In the specialized expression [e], the type vars and regions introduced
    by the substitution will appear in the [e.e_vty], but not in the range
    of [e.e_tvs] and [e.e_regs], as they are related to no ident.

  - The invariant <*> above is not verified explicitly, but is maintained
    by construction of ppsymbols. In particular, every extra type var and
    region in [e.e_vty] appear in the range of [e.e_tvs] and [e.e_regs].
*)

