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
  pv_vs  : vsymbol;
  pv_vtv : vty_value;
}

module Pv = Util.StructMake (struct
  type t = pvsymbol
  let tag pv = Hashweak.tag_hash pv.pv_vs.vs_name.id_tag
end)

module Spv = Pv.S
module Mpv = Pv.M

let pv_equal : pvsymbol -> pvsymbol -> bool = (==)

let create_pvsymbol id vtv = {
  pv_vs   = create_vsymbol id (ty_of_ity vtv.vtv_ity);
  pv_vtv  = vtv;
}

type pasymbol = {
  pa_name : ident;
  pa_vta  : vty_arrow;
  pa_tvs  : Stv.t;
  pa_regs : Sreg.t;
}

let pa_equal : pasymbol -> pasymbol -> bool = (==)

(** program symbols *)

type psymbol = {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_tvs   : Stv.t;
  ps_regs  : Sreg.t;
  ps_subst : ity_subst;
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

type expr = {
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
  | Earrow  of pasymbol
  | Einst   of psymbol * ity_subst
  | Eapp    of pasymbol * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of pvsymbol * expr * expr
  | Eassign of pvsymbol * pvsymbol (* mutable pv <- expr *)
  | Eany

and let_defn = {
  let_var  : let_var;
  let_expr : expr;
}

and let_var =
  | LetV of pvsymbol
  | LetA of pasymbol

and rec_defn = {
  rec_ps     : psymbol;
  rec_lambda : lambda;
}

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : pre;
  l_expr    : expr;
  l_post    : post;
  l_xpost   : xpost;
}

and variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}


(* smart constructors *)

let e_label ?loc l e = { e with e_label = l; e_loc = loc }

let e_label_add l e = { e with e_label = Slab.add l e.e_label }

let e_label_copy { e_label = lab; e_loc = loc } e =
  let lab = Slab.union lab e.e_label in
  let loc = if e.e_loc = None then loc else e.e_loc in
  { e with e_label = lab; e_loc = loc }

(* FIXME: this is ugly *)
let e_dummy node vty = {
  e_node   = node;
  e_vty    = vty;
  e_effect = eff_empty;
  e_tvs    = Mid.empty;
  e_regs   = Mid.empty;
  e_label  = Slab.empty;
  e_loc    = None;
}

let add_pv_tvs s pv  = Mid.add pv.pv_vs.vs_name pv.pv_vtv.vtv_tvs s
let add_pv_regs s pv = Mid.add pv.pv_vs.vs_name pv.pv_vtv.vtv_regs s

let add_pa_tvs s pa  = Mid.add pa.pa_name pa.pa_tvs s
let add_pa_regs s pa = Mid.add pa.pa_name pa.pa_regs s

let add_expr_tvs m e =
  Mid.union (fun _ s1 s2 -> Some (Stv.union s1 s2)) m e.e_tvs

let add_expr_regs m e =
  Mid.union (fun _ s1 s2 -> Some (Sreg.union s1 s2)) m e.e_regs

let e_value pv =
  { (e_dummy (Elogic (t_var pv.pv_vs)) (VTvalue pv.pv_vtv)) with
    e_tvs  = add_pv_tvs Mid.empty pv;
    e_regs = add_pv_regs Mid.empty pv; }

let e_arrow pa =
  { (e_dummy (Earrow pa) (VTarrow pa.pa_vta)) with
    e_tvs  = add_pa_tvs Mid.empty pa;
    e_regs = add_pa_regs Mid.empty pa; }

let e_inst ps sbs =
  let vty =
    if not (Mtv.is_empty sbs.ity_subst_tv && Mreg.is_empty sbs.ity_subst_reg)
    then VTarrow (vta_full_inst (ity_subst_union ps.ps_subst sbs) ps.ps_vta)
    else VTarrow ps.ps_vta
  in
  { (e_dummy (Einst (ps,sbs)) vty) with
    e_tvs  = Mid.singleton ps.ps_name ps.ps_tvs;
    e_regs = Mid.singleton ps.ps_name ps.ps_regs; }
  (* we only count the fixed type variables and regions of ps, so that
     type variables and regions introduced by the substitution could be
     generalized in this expression *)

exception GhostWrite of expr * region
exception GhostRaise of expr * xsymbol

let ghost_effect e =
  if vty_ghost e.e_vty then
    let eff = e.e_effect in
    let check r = not r.reg_ghost in
    if Sreg.exists check eff.eff_writes then
      let s = Sreg.filter check eff.eff_writes in
      raise (GhostWrite (e, Sreg.choose s))
    else e
  else e

let e_app pa pv =
  let eff,vty = vty_app_arrow pa.pa_vta pv.pv_vtv in
  ghost_effect { (e_dummy (Eapp (pa,pv)) vty) with
    e_effect = eff;
    e_tvs    = add_pv_tvs (add_pa_tvs Mid.empty pa) pv;
    e_regs   = add_pv_regs (add_pa_regs Mid.empty pa) pv; }

let create_let_defn id e =
  let lv = match e.e_vty with
    | VTvalue vtv -> LetV (create_pvsymbol id vtv)
    | VTarrow vta -> LetA {
        pa_name = Ident.id_register id;
        pa_vta  = vta;
        pa_tvs  = Mid.fold (fun _ -> Stv.union)  e.e_tvs  vta.vta_tvs;
        pa_regs = Mid.fold (fun _ -> Sreg.union) e.e_regs vta.vta_regs; }
  in
  { let_var = lv ; let_expr = e }

exception StaleRegion of region * ident * expr

let e_let ({ let_var = lv ; let_expr = d } as ld) e =
  let eff = d.e_effect in
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA pa -> pa.pa_name
  in
  let tvs = Mid.remove id e.e_tvs in
  let regs = Mid.remove id e.e_regs in
  (* If we reset some region in the first expression d, then it may only
     pccur in the second expression e in association to pv. Otherwise,
     this is a freshness violation: some symbol defined earlier carries
     that region into e. *)
  (* FIXME? bad complexity, we should be able to do better *)
  let check_reset r u = (* does r occur in e? *)
    let check_id id s = (* does r occur among the regions of id? *)
      let rec check_reg reg =
        reg_equal r reg || match u with
          | Some u when reg_equal u reg -> false
          | _ -> ity_v_any Util.ffalse check_reg reg.reg_ity
      in
      if Sreg.exists check_reg s then raise (StaleRegion (r,id,e))
    in
    Mid.iter check_id regs
  in
  Mreg.iter check_reset eff.eff_resets;
  (* We should be able to raise and catch exceptions inside ghost expressions.
     The problematic case is a ghost exception that escapes into reality. *)
  (* FIXME: this test is too restrictive. If this let is embedded into a
     bigger ghost expression, then an exception raised from d and catched
     there is benign. A good test is to traverse top-level definitions
     from top to bottom and check if exceptions escape from the outermost
     ghost subexpressions. *)
  if vty_ghost d.e_vty && not (vty_ghost e.e_vty) &&
      not (Sexn.is_empty eff.eff_raises) then
    raise (GhostRaise (e, Sexn.choose eff.eff_raises));
  (* This should be the only expression constructor that deals with
     sequence of effects *)
  ghost_effect { (e_dummy (Elet (ld,e)) e.e_vty) with
    e_effect = eff_union d.e_effect e.e_effect;
    e_tvs    = add_expr_tvs tvs d;
    e_regs   = add_expr_regs regs d; }

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

