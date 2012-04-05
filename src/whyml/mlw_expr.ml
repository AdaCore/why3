(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

(* program symbols *)
type psymbol = {
  p_name : ident;
  p_tvs  : Stv.t;
  p_reg  : Sreg.t;
  p_vty  : vty;
}

let create_psymbol id tvars regs = function
  | VTvalue pv ->
      let pv =
        create_pvsymbol id ?mut:pv.pv_mutable ~ghost:pv.pv_ghost pv.pv_ity in
      { p_name = pv.pv_vs.vs_name;
        p_tvs = tvars; p_reg = regs; p_vty = vty_value pv; }
  | VTarrow _ as vty ->
      (* TODO? check that tvars/regs are in vty *)
      { p_name = id_register id; p_tvs = tvars; p_reg = regs; p_vty = vty; }

let ps_equal : psymbol -> psymbol -> bool = (==)

type expr = private {
  e_node  : expr_node;
  e_vty   : vty;
  e_eff   : effect;
  e_ghost : bool;
  e_label : Slab.t;
  e_loc   : Loc.position option;
}

and expr_node =
  | Elogic  of term
  | Esym    of psymbol (* function *)
  | Eapp    of psymbol * expr
  | Elet    of psymbol * expr * expr
  | Eletrec of recfun list * expr
  | Efun    of lambda
  | Eif     of expr * expr * expr
  | Eassign of pvsymbol * psymbol * region * expr (* e1.f<rho> <- e2 *)

and recfun = psymbol * lambda

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : term;
  l_body    : expr;
  l_post    : term;
  l_xpost   : xpost;
}

let lapp _ = assert false (*TODO*)
let papp _ = assert false (*TODO*)
let app _ = assert false (*TODO*)
let plet _ = assert false (*TODO*)
let pletrec _ = assert false (*TODO*)
let pfun _ = assert false (*TODO*)
let assign _ = assert false (*TODO*)

