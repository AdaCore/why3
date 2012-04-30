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
type xpost = post Mexn.t (* exceptional postconditions *)

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
  | Evalue  of pvsymbol
  | Earrow  of pasymbol
  | Einst   of psymbol
  | Eapp    of pasymbol * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of pvsymbol * expr * expr
  | Eassign of pvsymbol * region * pvsymbol (* mutable pv <- expr *)
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
  rec_tvs    : Stv.t Mid.t;
  rec_regs   : Sreg.t Mid.t;
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

let mk_expr node vty eff tvs regs =
  ghost_effect {
    e_node   = node;
    e_vty    = vty;
    e_effect = eff;
    e_tvs    = tvs;
    e_regs   = regs;
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
  let tvs = add_pv_tvs Mid.empty pv in
  let regs = add_pv_regs Mid.empty pv in
  mk_expr (Evalue pv) (VTvalue pv.pv_vtv) eff_empty tvs regs

let e_arrow pa =
  let tvs = add_pa_tvs Mid.empty pa in
  let regs = add_pa_regs Mid.empty pa in
  mk_expr (Earrow pa) (VTarrow pa.pa_vta) eff_empty tvs regs

let e_inst ps sbs =
  (* we only count the fixed type variables and regions of ps, so that
     type variables and regions introduced by the substitution could be
     generalized in this expression *)
  let tvs = Mid.singleton ps.ps_name ps.ps_tvs in
  let regs = Mid.singleton ps.ps_name ps.ps_regs in
  let vta =
    if not (Mtv.is_empty sbs.ity_subst_tv && Mreg.is_empty sbs.ity_subst_reg)
    then vta_full_inst (ity_subst_union ps.ps_subst sbs) ps.ps_vta
    else ps.ps_vta
  in
  mk_expr (Einst ps) (VTarrow vta) eff_empty tvs regs

let e_app_real pa pv =
  let tvs = add_pv_tvs (add_pa_tvs Mid.empty pa) pv in
  let regs = add_pv_regs (add_pa_regs Mid.empty pa) pv in
  let eff,vty = vty_app_arrow pa.pa_vta pv.pv_vtv in
  mk_expr (Eapp (pa,pv)) vty eff tvs regs

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
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA pa -> pa.pa_name
  in
  let tvs = Mid.remove id e.e_tvs in
  let regs = Mid.remove id e.e_regs in
  (* If we reset some region in the first expression d, then it may only
     occur in the second expression e in association to pv. Otherwise,
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
  Mreg.iter check_reset d.e_effect.eff_resets;
  (* We should be able to raise and catch exceptions inside ghost expressions.
     The problematic case is a ghost exception that escapes into reality. *)
  (* FIXME: this test is too restrictive. If this let is embedded into a
     bigger ghost expression, then an exception raised from d and catched
     there is benign. A good test is to traverse top-level definitions
     from top to bottom and check if exceptions escape from the outermost
     ghost subexpressions. *)
  if vty_ghost d.e_vty && not (vty_ghost e.e_vty) &&
      not (Sexn.is_empty d.e_effect.eff_raises) then
    raise (GhostRaise (d, Sexn.choose d.e_effect.eff_raises));
  (* This should be the only expression constructor that deals with
     sequence of effects *)
  let tvs = add_expr_tvs tvs d in
  let regs = add_expr_regs regs d in
  let eff = eff_union d.e_effect e.e_effect in
  mk_expr (Elet (ld,e)) e.e_vty eff tvs regs

let create_post vs f = t_eps_close vs f

let open_post f = match f.t_node with
  | Teps bf -> t_open_bound bf
  | _ -> assert false

let create_fun_defn id lam =
  (* sanity check *)
  if lam.l_pre.t_ty <> None then raise (FmlaExpected lam.l_pre);
  let check_post ity post =
    let ty = ty_of_ity ity in
    if not (ty_equal ty (t_type post)) then
      raise (Ty.TypeMismatch (ty, t_type post))
  in
  begin match lam.l_expr.e_vty with
    | VTvalue vtv -> check_post vtv.vtv_ity lam.l_post
    | VTarrow _ -> ()
    (* FIXME? Should we check that the bound variable does not occur
       in the postcondition formula when lam.l_expr.e_vty is an arrow? *)
  end;
  Mexn.iter (fun xs t -> check_post xs.xs_ity t) lam.l_xpost;
  if lam.l_variant <> [] then
    Loc.errorm "Variants are not allowed in a non-recursive definition";
  (* compute rec_tvs and rec_regs *)
  let tyvars s = Util.def_option Stv.empty s in
  let add vs s = Some (ty_freevars (tyvars s) vs.vs_ty) in
  let add vs _ m = Mid.change (add vs) vs.vs_name m in
  let add_term_tvs t m = Mvs.fold add t.t_vars m in
  let remove_pv m pv = Mid.remove pv.pv_vs.vs_name m in
  let rectvs = lam.l_expr.e_tvs in
  let rectvs = add_term_tvs lam.l_pre rectvs in
  let rectvs = add_term_tvs lam.l_post rectvs in
  let rectvs = Mexn.fold (fun _ -> add_term_tvs) lam.l_xpost rectvs in
  let rectvs = List.fold_left remove_pv rectvs lam.l_args in
  let recregs = List.fold_left remove_pv lam.l_expr.e_regs lam.l_args in
  (* compute rec_ps.ps_tvs/regs/subst *)
  let tvs = Mid.fold (fun _ -> Stv.union) rectvs Stv.empty in
  let regs = Mid.fold (fun _ -> Sreg.union) recregs Sreg.empty in
  let fix_tv tv subst = let ty = ity_var tv in ity_match subst ty ty in
  let fix_reg reg subst = reg_match subst reg reg in
  let subst = Stv.fold fix_tv tvs ity_subst_empty in
  let subst = Sreg.fold fix_reg regs subst in
  (* compute rec_ps.ps_vta *)
  let e = lam.l_expr in
  let arg, argl = match List.rev lam.l_args with
    | [] -> Loc.errorm "Empty argument list"
    | arg::argl -> arg, argl in
  let vta = vty_arrow arg.pv_vtv ~effect:e.e_effect e.e_vty in
  let add_arg vta pv = vty_arrow pv.pv_vtv (VTarrow vta) in
  let vta = List.fold_left add_arg vta argl in
  (* construct rec_ps and rec_defn *)
  let ps = {
    ps_name  = id_register id;
    ps_vta   = vta;
    ps_tvs   = tvs;
    ps_regs  = regs;
    ps_subst = subst; }
  in {
    rec_ps     = ps;
    rec_lambda = lam;
    rec_tvs    = rectvs;
    rec_regs   = recregs; }

let e_rec rdl e =
  let add_tvs m rd =
    Mid.union (fun _ s1 s2 -> Some (Stv.union s1 s2)) m rd.rec_tvs in
  let add_regs m rd =
    Mid.union (fun _ s1 s2 -> Some (Sreg.union s1 s2)) m rd.rec_regs in
  let tvs = List.fold_left add_tvs e.e_tvs rdl in
  let regs = List.fold_left add_regs e.e_regs rdl in
  let remove_ps m rd = Mid.remove rd.rec_ps.ps_name m in
  let tvs = List.fold_left remove_ps tvs rdl in
  let regs = List.fold_left remove_ps regs rdl in
  mk_expr (Erec (rdl,e)) e.e_vty e.e_effect tvs regs

exception ValueExpected of expr
exception ArrowExpected of expr

let on_value fn e = match e.e_node with
  | Evalue pv -> fn pv
  | _ ->
      let ld = create_let_defn (id_fresh "o") e in
      let pv = match ld.let_var with
        | LetA _ -> raise (ValueExpected e)
        | LetV pv -> pv
      in
      e_let ld (fn pv)

let on_arrow fn e = match e.e_node with
  | Earrow pa -> fn pa
  | _ ->
      let ld = create_let_defn (id_fresh "o") e in
      let pa = match ld.let_var with
        | LetV _ -> raise (ArrowExpected e)
        | LetA pa -> pa
      in
      e_let ld (fn pa)

(* We adopt right-to-left evaluation order so that expression
     get_ref (create_ref 5)
   produces
     let pv : ref<ro> int =
        let pv1 : int = Elogic 5 in
        let pa1 : int -> ref<ro> int = Einst create_ref in
        Eapp pa1 pv1 [reset ro]
     in
     let pa : ref<ro> int -> int = Einst get_ref in
     Eapp pa pv [read ro]
   which is ok. If pa is computed before pv, then Eapp pa pv would
   violate the freshness of ro.

   FIXME? This means that some reasonable programs, such as
     let local_get_ref = get_ref in
     let my_ref = create_ref 5 in
     local_get_ref my_ref
   will be rejected, since local_get_ref is instantiated to
   the region introduced (reset) by create_ref. Is it bad? *)

let e_app e el =
  let rec apply = function
    | [] -> e
    | e::el ->
        let app pv pa = e_app_real pa pv in
        let app pv = on_arrow (app pv) (apply el) in
        on_value app e
  in
  apply (List.rev el)

let e_plapp pls el ity =
  let rec app tl tvs regs ghost sbs vtvl argl =
    match vtvl, argl with
      | [],[] ->
          let vtv = pls.pl_value in
          let ghost = ghost || vtv.vtv_ghost in
          let sbs = ity_match sbs vtv.vtv_ity ity in
          let mut = Util.option_map (reg_full_inst sbs) vtv.vtv_mut in
          let vty = VTvalue (vty_value ~ghost ?mut ity) in
          let eff = eff_full_inst sbs pls.pl_effect in
(* FIXME? We will need to check later in Mlw_module that all symbols
   we use are defined: including lsymbols, plsymbols, itysymbols,
   and tysymbols. We can care about lsymbols and plsymbols here.
   What should we do about type symbols? *)
          let tvs = Mid.add pls.pl_ls.ls_name Mtv.empty tvs in
          let regs = Mid.add pls.pl_ls.ls_name Mreg.empty regs in
          let t = match pls.pl_ls.ls_value with
            | Some _ -> fs_app pls.pl_ls tl (ty_of_ity ity)
            | None   -> ps_app pls.pl_ls tl in
          mk_expr (Elogic t) vty eff tvs regs
      | [],_ | _,[] ->
          raise (Term.BadArity
            (pls.pl_ls, List.length pls.pl_args, List.length el))
      | vtv::vtvl, ({ e_node = Elogic t } as e)::argl ->
          let tvs = add_expr_tvs tvs e in
          let regs = add_expr_regs regs e in
          let evtv = match e.e_vty with
            | VTvalue vtv -> vtv
            | VTarrow _   -> assert false in
          let ghost = ghost || (evtv.vtv_ghost && not vtv.vtv_ghost) in
          let sbs = ity_match sbs vtv.vtv_ity evtv.vtv_ity in
          app (t::tl) tvs regs ghost sbs vtvl argl
      | vtv::vtvl, e::argl ->
          let apply_to_pv pv =
            let tvs = add_pv_tvs tvs pv in
            let regs = add_pv_regs regs pv in
            let ghost = ghost || (pv.pv_vtv.vtv_ghost && not vtv.vtv_ghost) in
            let sbs = ity_match sbs vtv.vtv_ity pv.pv_vtv.vtv_ity in
            app (t_var pv.pv_vs :: tl) tvs regs ghost sbs vtvl argl
          in
          on_value apply_to_pv e
  in
  let vtvl = List.rev pls.pl_args in
  let argl = List.rev el in
  app [] Mid.empty Mid.empty false ity_subst_empty vtvl argl

let e_lapp ls el ity =
  let pls = {
    pl_ls     = ls;
    pl_args   = List.map (fun ty -> vty_value (ity_of_ty ty)) ls.ls_args;
    pl_value  = vty_value (ity_of_ty (Util.def_option ty_bool ls.ls_value));
    pl_effect = eff_empty; }
  in
  e_plapp pls el ity

let vtv_of_expr e = match e.e_vty with
  | VTvalue vtv -> vtv
  | VTarrow _ -> raise (ValueExpected e)

let e_if_real pv e1 e2 =
  let vtv1 = vtv_of_expr e1 in
  let vtv2 = vtv_of_expr e2 in
  ity_equal_check vtv1.vtv_ity vtv2.vtv_ity;
  ity_equal_check pv.pv_vtv.vtv_ity ity_bool;
  let eff = eff_union e1.e_effect e2.e_effect in
  let tvs = add_expr_tvs (add_expr_tvs (add_pv_tvs Mid.empty pv) e1) e2 in
  let regs = add_expr_regs (add_expr_regs (add_pv_regs Mid.empty pv) e1) e2 in
  let ghost = pv.pv_vtv.vtv_ghost || vtv1.vtv_ghost || vtv2.vtv_ghost in
  let vty = VTvalue (vty_value ~ghost vtv1.vtv_ity) in
  mk_expr (Eif (pv,e1,e2)) vty eff tvs regs

let e_if e e1 e2 = on_value (fun pv -> e_if_real pv e1 e2) e

exception Immutable of pvsymbol

let e_assign_real mpv pv =
  let r = match mpv.pv_vtv.vtv_mut with
    | Some r -> r
    | None -> raise (Immutable mpv)
  in
  let eff = eff_assign eff_empty r pv.pv_vtv.vtv_ity in
  let tvs = add_pv_tvs (add_pv_tvs Mid.empty mpv) pv in
  let regs = add_pv_regs (add_pv_regs Mid.empty mpv) pv in
  let ghost = mpv.pv_vtv.vtv_ghost || pv.pv_vtv.vtv_ghost in
  let vty = VTvalue (vty_value ~ghost ity_unit) in
  mk_expr (Eassign (mpv,r,pv)) vty eff tvs regs

let e_assign me e =
  let assign pv mpv = e_assign_real mpv pv in
  let assign pv = on_value (assign pv) me in
  on_value assign e

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

