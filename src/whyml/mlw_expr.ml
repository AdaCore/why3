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

  1. A "proper type" of a vty [v] is [v] with all effects and specs
     (pre/post/xpost) removed. Basically, it is formed from the ity's
     of pvsymbols in the arguments and the result of [v].

  2. Given a vty [v], [vty_freevars v] and [vty_topregions v] return 
     the sets of type variables and regions, respectively, that occur 
     in the proper type of [v]. We will call them "proper" type variables
     and regions of [v].

  3. The specs (pre/post/xpost) and the effects in a vty [v] may contain
     type variables and regions that do not occur in the proper type of [v].
     We will call them "extra" type variables and regions of [v].

  4. A substitution given to [vty_full_inst] MUST instantiate every extra
     type variable and region to itself. We do not verify this invariant,
     but it is going to be ensured by the following.

  5. An expression [e] provides the maps [e.e_tvs] and [e.e_regs] from
     idents (vsymbols, pvsymbols, psymbols, ppsymbols) occurring in [e]
     to sets of type variables and regions, respectively, that are 
     "related" to these idents. For example, every type variable and
     region that occurs in a pv_ity of a pvsymbol [x] is related to [x].
     For psymbols and ppsymbols, the meaning of "related" is explained below.

  6. It is possible that [e.e_vty] contains a proper type variable or 
     a proper region that does not appear in the range of [e.e_tvs] or 
     [e.e_regs]. However, every extra type variable and region of
     [e.e_vty] MUST occur in the range of [e.e_tvs] and [e.e_regs].

  7. A psymbol (monomorphic program symbol) [p] provides the sets [p.p_tvs]
     and [p.p_regs] of its related type variables and regions, respectively, 
     that cover both proper and extra type variables and regions of [p.p_vty].

     One way to ensure this is to put into [p.p_tvs] the union of the proper
     type variables of [p.p_vty] and all the type variables in the range of
     [e.e_tvs], where [e] is the defining expression of [p] (similarly for
     regions). However, this will relate to [p] more that just proper and
     extra variables of [p.p_vty]. It is unclear whether this is a problem,
     but my guess is it's not.

  8. A ppsymbol  
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

