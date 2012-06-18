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
open Util
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T

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

let create_pvsymbol, restore_pv =
  let vs_to_pv = Wvs.create 17 in
  (fun id vtv ->
    let pv = create_pvsymbol id vtv in
    Wvs.set vs_to_pv pv.pv_vs pv;
    pv),
  (fun vs -> try Wvs.find vs_to_pv vs with
    Not_found -> raise (Decl.UnboundVar vs))

(** program symbols *)

type psymbol = {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_vars  : varset;
  ps_subst : ity_subst;
}

let ps_equal : psymbol -> psymbol -> bool = (==)

let create_psymbol id vta vars = {
  ps_name  = id_register id;
  ps_vta   = vta_filter vars vta;
  ps_vars  = vars;
  ps_subst = vars_freeze vars;
}

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
  let eff_read e r = eff_read e ~ghost:value.vtv_ghost r in
  let effect = Util.option_fold eff_read eff_empty value.vtv_mut in
  let arg_reset acc a = Util.option_fold eff_reset acc a.vtv_mut in
  let effect = List.fold_left arg_reset effect args in {
    pl_ls     = ls;
    pl_args   = args;
    pl_value  = value;
    pl_effect = effect;
  }

(** specification *)

type pre   = term (* precondition *)
type post  = term (* postcondition *)
type xpost = post Mexn.t (* exceptional postconditions *)

type type_c = {
  c_pre    : pre;
  c_effect : effect;
  c_result : type_v;
  c_post   : post;
  c_xpost  : xpost;
}

and type_v =
  | SpecV of vty_value
  | SpecA of pvsymbol list * type_c

type let_var =
  | LetV of pvsymbol
  | LetA of psymbol

type val_decl = {
  val_name : let_var;
  val_spec : type_v;
  val_vars : varset Mid.t;
}

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

let create_post vs f = t_eps_close vs f

let open_post f = match f.t_node with
  | Teps bf -> t_open_bound bf
  | _ -> assert false

let varmap_join = Mid.fold (fun _ -> vars_union)
let varmap_union = Mid.set_union

let add_pv_vars pv m = Mid.add pv.pv_vs.vs_name pv.pv_vtv.vtv_vars m
let add_vs_vars vs m = add_pv_vars (restore_pv vs) m

let spec_vars varm variant pre post xpost _effect result =
  (* sanity check *)
  if pre.t_ty <> None then raise (FmlaExpected pre);
  let check_post ity post =
    let ty = ty_of_ity ity in
    if not (ty_equal ty (t_type post)) then
      raise (Ty.TypeMismatch (ty, t_type post))
  in
  begin match result with
    | Some vtv -> check_post vtv.vtv_ity post
    | None -> ()
    (* FIXME? Should we check that the bound variable does not occur
       in the postcondition formula when result is an arrow? *)
  end;
  (* FIXME? Should we check that every raised exception is in xpost? *)
  Mexn.iter (fun xs t -> check_post xs.xs_ity t) xpost;
  (* compute rec_vars and ps.ps_vars *)
  let add_term t s = Mvs.set_union t.t_vars s in
  let add_variant { v_term = t; v_rel = ps } s =
    ignore (Util.option_map (fun ps -> ps_app ps [t;t]) ps);
    add_term t s in
  let vsset = add_term post (add_term pre Mvs.empty) in
  let vsset = Mexn.fold (fun _ -> add_term) xpost vsset in
  let vsset = List.fold_right add_variant variant vsset in
  Mvs.fold (fun vs _ m -> add_vs_vars vs m) vsset varm

let spec_arrow pvl effect vty =
  let arg,argl = match List.rev pvl with
    | [] -> Loc.errorm "Empty argument list"
    | arg::argl -> arg, argl in
  let vta = vty_arrow arg.pv_vtv ~effect vty in
  let add_arg vta pv = vty_arrow pv.pv_vtv (VTarrow vta) in
  List.fold_left add_arg vta argl

let rec check_c tyc =
  let varm = check_v tyc.c_result in
  let result = match tyc.c_result with
    | SpecV v -> Some v
    | SpecA _ -> None in
  spec_vars varm [] tyc.c_pre tyc.c_post tyc.c_xpost tyc.c_effect result

and check_v = function
  | SpecV _ -> Mid.empty
  | SpecA (pvl,tyc) ->
      let del_pv m pv = Mid.remove pv.pv_vs.vs_name m in
      List.fold_left del_pv (check_c tyc) pvl

let eff_check vars result e =
  let check r =
    if not (reg_occurs r vars) then
      Loc.errorm "every external effect must be covered in a post-condition"
  in
  let reset r u = match result with
    | _ when u <> None -> Loc.errorm "abstract parameters cannot reset regions"
    | SpecV v when reg_occurs r v.vtv_vars -> ()
    | _ -> check r
  in
  Sreg.iter check e.eff_reads;
  Sreg.iter check e.eff_writes;
  Sreg.iter check e.eff_ghostr;
  Sreg.iter check e.eff_ghostw;
  Mreg.iter reset e.eff_resets

let rec build_c vars tyc =
  let vty = build_v vars tyc.c_result in
  eff_check vars tyc.c_result tyc.c_effect;
  vty

and build_v vars = function
  | SpecV vtv ->
      if vtv.vtv_mut <> None then
        Loc.errorm "abstract parameters cannot produce mutable values";
      VTvalue vtv
  | SpecA (pvl,tyc) ->
      let add_arg vars pv = vars_union vars pv.pv_vtv.vtv_vars in
      let vty = build_c (List.fold_left add_arg vars pvl) tyc in
      VTarrow (spec_arrow pvl tyc.c_effect vty)

let create_val id tyv =
  let varm = check_v tyv in
  let vars = varmap_join varm vars_empty in
  let name = match build_v vars tyv with
    | VTarrow vta -> LetA (create_psymbol id vta vars)
    | VTvalue vtv -> LetV (create_pvsymbol id vtv) in
  { val_name = name; val_spec = tyv; val_vars = varm }

(** patterns *)

type ppattern = {
  ppat_pattern : pattern;
  ppat_vtv     : vty_value;
  ppat_effect  : effect;
}

let ppat_wild vtv =
  if vtv.vtv_mut <> None then Loc.errorm "Wildcard patterns are immutable";
  { ppat_pattern = pat_wild (ty_of_ity vtv.vtv_ity);
    ppat_vtv     = vtv;
    ppat_effect  = eff_empty; }

let ppat_var pv =
  { ppat_pattern = pat_var pv.pv_vs;
    ppat_vtv     = pv.pv_vtv;
    ppat_effect  = eff_empty; }

let ppat_is_wild pp = match pp.ppat_pattern.pat_node with
  | Pwild -> true
  | _ -> false

let ppat_plapp pls ppl vtv =
  if vtv.vtv_mut <> None then
    Loc.errorm "Only variable patterns can be mutable";
  (* FIXME? Since pls is a constructor, the result type vtv will
     cover every type variable and region in the signature of pls.
     Then the following ity_match call is enough to build the full
     substitution. If, however, we are given a bad pls, say, a
     projection, then the following code may break with a less
     than understandable error message. Is it really important? *)
  let sbs = ity_match ity_subst_empty pls.pl_value.vtv_ity vtv.vtv_ity in
  let mtch eff arg pp =
    ignore (ity_match sbs arg.vtv_ity pp.ppat_vtv.vtv_ity);
    let ghost = pp.ppat_vtv.vtv_ghost in
    if ghost <> (vtv.vtv_ghost || arg.vtv_ghost) then
      Loc.errorm "Ghost pattern in a non-ghost context";
    let effect = eff_union eff pp.ppat_effect in
    match arg.vtv_mut, pp.ppat_vtv.vtv_mut with
    | _ when ppat_is_wild pp ->
        effect
    | Some r1, Some r2 ->
        ignore (reg_match sbs r1 r2);
        eff_read ~ghost effect (reg_full_inst sbs r1)
    | Some r1, None ->
        eff_read ~ghost effect (reg_full_inst sbs r1)
    | None, None ->
        effect
    | None, Some _ ->
        Loc.errorm "Mutable pattern in a non-mutable position"
  in
  let eff = try List.fold_left2 mtch eff_empty pls.pl_args ppl
    with Invalid_argument _ -> raise
      (Term.BadArity (pls.pl_ls, List.length pls.pl_args, List.length ppl)) in
  let pl = List.map (fun pp -> pp.ppat_pattern) ppl in
  { ppat_pattern = pat_app pls.pl_ls pl (ty_of_ity vtv.vtv_ity);
    ppat_vtv     = vtv;
    ppat_effect  = if vtv.vtv_ghost then eff_ghostify eff else eff; }

let ity_of_ty_opt ty = ity_of_ty (Util.def_option ty_bool ty)

let ppat_lapp ls ppl vtv =
  let pls = {
    pl_ls     = ls;
    pl_args   = List.map (fun ty -> vty_value (ity_of_ty ty)) ls.ls_args;
    pl_value  = vty_value (ity_of_ty_opt ls.ls_value);
    pl_effect = eff_empty; }
  in
  ppat_plapp pls ppl vtv

let ppat_or p1 p2 =
  ity_equal_check p1.ppat_vtv.vtv_ity p2.ppat_vtv.vtv_ity;
  if p1.ppat_vtv.vtv_ghost <> p2.ppat_vtv.vtv_ghost then
    Loc.errorm "Ghost pattern in a non-ghost context";
  if p1.ppat_vtv.vtv_mut <> None || p2.ppat_vtv.vtv_mut <> None then
    Loc.errorm "Mutable patterns are not allowed under OR";
  { ppat_pattern = pat_or p1.ppat_pattern p2.ppat_pattern;
    ppat_vtv     = p1.ppat_vtv;
    ppat_effect  = eff_union p1.ppat_effect p2.ppat_effect; }

let ppat_as pp pv =
  ity_equal_check pp.ppat_vtv.vtv_ity pv.pv_vtv.vtv_ity;
  if pp.ppat_vtv.vtv_ghost <> pv.pv_vtv.vtv_ghost then
    Loc.errorm "Ghost pattern in a non-ghost context";
  let vtv = match pp.ppat_vtv.vtv_mut, pv.pv_vtv.vtv_mut with
    | Some r1, Some r2 ->
        if not (reg_equal r1 r2) then raise (RegionMismatch (r1,r2));
        pp.ppat_vtv (* the two vtv's are identical *)
    | Some _, None -> pp.ppat_vtv
    | None, Some _ -> pv.pv_vtv
    | None, None -> pv.pv_vtv
  in
  { ppat_pattern = pat_as pp.ppat_pattern pv.pv_vs;
    ppat_vtv     = vtv;
    ppat_effect  = pp.ppat_effect; }

(* reconstruct a pattern from an untyped skeleton *)

type pre_ppattern =
  | PPwild
  | PPvar  of preid
  | PPlapp of lsymbol * pre_ppattern list
  | PPpapp of plsymbol * pre_ppattern list
  | PPor   of pre_ppattern * pre_ppattern
  | PPas   of pre_ppattern * preid

let make_ppattern pp vtv =
  let hv = Hashtbl.create 3 in
  let find id vtv =
    let nm = preid_name id in
    try
      let pv = Hashtbl.find hv nm in
      ity_equal_check vtv.vtv_ity pv.pv_vtv.vtv_ity;
      pv
    with Not_found ->
      let pv = create_pvsymbol id vtv in
      Hashtbl.add hv nm pv; pv
  in
  let rec make vtv = function
    | PPwild -> {
        ppat_pattern = pat_wild (ty_of_ity vtv.vtv_ity);
        ppat_vtv     = vtv_unmut vtv;
        ppat_effect  = eff_empty; }
    | PPvar id -> {
        ppat_pattern = pat_var (find id vtv).pv_vs;
        ppat_vtv     = vtv;
        ppat_effect  = eff_empty; }
    | PPpapp (pls,ppl) ->
        (* FIXME? Since pls is a constructor, the result type vtv will
           cover every type variable and region in the signature of pls.
           Then the following ity_match call is enough to build the full
           substitution. If, however, we are given a bad pls, say, a
           projection, then the following code may break with a less
           than understandable error message. Is it really important? *)
        let sbs = ity_match ity_subst_empty pls.pl_value.vtv_ity vtv.vtv_ity in
        let mtch arg pp =
          let ity = ity_full_inst sbs arg.vtv_ity in
          let ghost = vtv.vtv_ghost || arg.vtv_ghost in
          let mut = Util.option_map (reg_full_inst sbs) arg.vtv_mut in
          let pp = make (vty_value ~ghost ?mut ity) pp in
          if ppat_is_wild pp then pp.ppat_effect, pp else
          Util.option_fold (eff_read ~ghost) pp.ppat_effect mut, pp
        in
        let ppl = try List.map2 mtch pls.pl_args ppl with Invalid_argument _ ->
          raise (Term.BadArity
            (pls.pl_ls, List.length pls.pl_args, List.length ppl)) in
        let eff = List.fold_left
          (fun acc (eff,_) -> eff_union acc eff) eff_empty ppl in
        let pl = List.map (fun (_,pp) -> pp.ppat_pattern) ppl in
        { ppat_pattern = pat_app pls.pl_ls pl (ty_of_ity vtv.vtv_ity);
          ppat_vtv     = vtv_unmut vtv;
          ppat_effect  = if vtv.vtv_ghost then eff_ghostify eff else eff; }
    | PPlapp (ls,ppl) ->
        let ity = ity_of_ty_opt ls.ls_value in
        let sbs = ity_match ity_subst_empty ity vtv.vtv_ity in
        let mtch arg pp =
          let ity = ity_full_inst sbs (ity_of_ty arg) in
          make (vty_value ~ghost:vtv.vtv_ghost ity) pp
        in
        let ppl = try List.map2 mtch ls.ls_args ppl with Invalid_argument _ ->
          raise (Term.BadArity (ls,List.length ls.ls_args,List.length ppl)) in
        let eff = List.fold_left
          (fun acc pp -> eff_union acc pp.ppat_effect) eff_empty ppl in
        let pl = List.map (fun pp -> pp.ppat_pattern) ppl in
        { ppat_pattern = pat_app ls pl (ty_of_ity vtv.vtv_ity);
          ppat_vtv     = vtv_unmut vtv;
          ppat_effect  = if vtv.vtv_ghost then eff_ghostify eff else eff; }
    | PPor (pp1,pp2) ->
        let vtv = vtv_unmut vtv in
        let pp1 = make vtv pp1 in
        let pp2 = make vtv pp2 in
        { ppat_pattern = pat_or pp1.ppat_pattern pp2.ppat_pattern;
          ppat_vtv     = vtv;
          ppat_effect  = eff_union pp1.ppat_effect pp2.ppat_effect; }
    | PPas (pp,id) ->
        let pp = make vtv pp in
        { ppat_pattern = pat_as pp.ppat_pattern (find id vtv).pv_vs;
          ppat_vtv     = vtv_unmut vtv;
          ppat_effect  = pp.ppat_effect; }
  in
  let pp = make (vtv_unmut vtv) pp in
  Hashtbl.fold Mstr.add hv Mstr.empty, pp

(** program expressions *)

type assertion_kind = Aassert | Aassume | Acheck

type expr = {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_vars   : varset Mid.t;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Elogic  of term
  | Evalue  of pvsymbol
  | Earrow  of psymbol
  | Eapp    of expr * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (ppattern * expr) list
  | Eassign of expr * region * pvsymbol
  | Eghost  of expr
  | Eany    of type_c
  | Eraise  of xsymbol * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eassert of assertion_kind * term
  | Eabsurd

and let_defn = {
  let_var  : let_var;
  let_expr : expr;
}

and rec_defn = {
  rec_ps     : psymbol;
  rec_lambda : lambda;
  rec_vars   : varset Mid.t;
}

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : pre;
  l_expr    : expr;
  l_post    : post;
  l_xpost   : xpost;
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

let mk_expr node vty eff vars = {
  e_node   = node;
  e_vty    = vty;
  e_effect = if vty_ghost vty then eff_ghostify eff else eff;
  e_vars   = vars;
  e_label  = Slab.empty;
  e_loc    = None;
}

let add_t_vars t m = Mvs.fold (fun vs _ m -> add_vs_vars vs m) t.t_vars m
let add_e_vars e m = varmap_union e.e_vars m

let e_value pv =
  mk_expr (Evalue pv) (VTvalue pv.pv_vtv) eff_empty (add_pv_vars pv Mid.empty)

let e_inst ps sbs =
  (* we only count the fixed type variables and regions of ps, so that
     type variables and regions introduced by the substitution could be
     generalized in this expression *)
  let vars = Mid.singleton ps.ps_name ps.ps_vars in
  let vta = vta_full_inst (ity_subst_union ps.ps_subst sbs) ps.ps_vta in
  mk_expr (Earrow ps) (VTarrow vta) eff_empty vars

let e_cast ps vty =
  let rec vty_match sbs t1 t2 = match t1,t2 with
    | VTvalue v1, VTvalue v2 ->
        ity_match sbs v1.vtv_ity v2.vtv_ity
    | VTarrow a1, VTarrow a2 ->
        let sbs = ity_match sbs a1.vta_arg.vtv_ity a2.vta_arg.vtv_ity in
        vty_match sbs a1.vta_result a2.vta_result
    | _ -> invalid_arg "Mlw_expr.e_cast"
  in
  let sbs = vty_match ps.ps_subst (VTarrow ps.ps_vta) vty in
  let vars = Mid.singleton ps.ps_name ps.ps_vars in
  let vta = vta_full_inst sbs ps.ps_vta in
  mk_expr (Earrow ps) (VTarrow vta) eff_empty vars

let create_let_defn id e =
  let lv = match e.e_vty with
    | VTvalue vtv ->
        LetV (create_pvsymbol id (vtv_unmut vtv))
    | VTarrow vta ->
        LetA (create_psymbol id vta (varmap_join e.e_vars vta.vta_vars))
  in
  { let_var = lv ; let_expr = e }

exception StaleRegion of region * ident

let check_reset e vars =
  (* If we reset a region, then it may only occur in the later code
     as the result of the resetting expression. Otherwise, this is
     a freshness violation: some symbol defined earlier carries that
     region into the later code. *)
  let check_reset r u = (* does r occur in vars? *)
    let check_id id s = (* does r occur among the regions of id? *)
      let rec check_reg reg =
        reg_equal r reg || match u with
          | Some u when reg_equal u reg -> false
          | _ -> ity_v_any Util.ffalse check_reg reg.reg_ity
      in
      if Sreg.exists check_reg s.vars_reg then raise (StaleRegion (r,id))
    in
    Mid.iter check_id vars
  in
  Mreg.iter check_reset e.e_effect.eff_resets

let check_ghost_write e eff =
  (* If we make a ghost write, then the modified region cannot
     be read in a later non-ghost code. We ignore any resets:
     a once ghostified region must stay so, even if it is reset. *)
  let badwr = Sreg.inter e.e_effect.eff_ghostw eff.eff_reads in
  if not (Sreg.is_empty badwr) then raise (GhostWrite (e, Sreg.choose badwr))

let check_postexpr e eff vars =
  check_ghost_write e eff;
  check_reset e vars

let e_let ({ let_var = lv ; let_expr = d } as ld) e =
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA ps -> ps.ps_name in
  let vars = Mid.remove id e.e_vars in
  check_postexpr d e.e_effect vars;
  let eff = eff_union d.e_effect e.e_effect in
  mk_expr (Elet (ld,e)) e.e_vty eff (add_e_vars d vars)

exception ValueExpected of expr
exception ArrowExpected of expr

let e_app_real e pv =
  let vta = match e.e_vty with
    | VTarrow vta -> vta
    | VTvalue _ -> raise (ArrowExpected e)
  in
  let eff,vty = vty_app_arrow vta pv.pv_vtv in
  check_postexpr e eff (add_pv_vars pv Mid.empty);
  let eff = eff_union e.e_effect eff in
  mk_expr (Eapp (e,pv)) vty eff (add_pv_vars pv e.e_vars)

let create_fun_defn id lam =
  let e = lam.l_expr in
  let result = match e.e_vty with
    | VTvalue v -> Some v
    | VTarrow _ -> None in
  let varm = spec_vars e.e_vars lam.l_variant
      lam.l_pre lam.l_post lam.l_xpost e.e_effect result in
  let del_pv m pv = Mid.remove pv.pv_vs.vs_name m in
  let varm = List.fold_left del_pv varm lam.l_args in
  let vars = varmap_join varm vars_empty in
  let vta = spec_arrow lam.l_args e.e_effect e.e_vty in
  (* construct rec_defn *)
  { rec_ps     = create_psymbol id vta vars;
    rec_lambda = lam;
    rec_vars   = varm; }

let e_rec rdl e =
  let add_vars m rd = varmap_union m rd.rec_vars in
  let remove_ps m rd = Mid.remove rd.rec_ps.ps_name m in
  let vars = List.fold_left add_vars e.e_vars rdl in
  let vars = List.fold_left remove_ps vars rdl in
  mk_expr (Erec (rdl,e)) e.e_vty e.e_effect vars

let on_value fn e = match e.e_node with
  | Evalue pv -> fn pv
  | _ ->
      let ld = create_let_defn (id_fresh "o") e in
      let pv = match ld.let_var with
        | LetA _ -> raise (ValueExpected e)
        | LetV pv -> pv in
      e_let ld (fn pv)

(* We adopt right-to-left evaluation order so that expression
     get_ref (create_ref 5)
   produces
     let pv : ref<ro> int =
        let pv1 : int = Elogic 5 in
        Eapp (Earrow create_ref) pv1 [reset ro]
     in
     Eapp (Earrow get_ref) pv [read ro]
   which is ok. If (Earrow get_ref) is computed before pv,
   the second application would violate the freshness of ro.

   FIXME? This means that some reasonable programs, such as
     let local_get_ref = get_ref in
     let my_ref = create_ref 5 in
     local_get_ref my_ref
   will be rejected, since local_get_ref is instantiated to
   the region introduced (reset) by create_ref. Is it bad? *)

let e_app = List.fold_left (fun e -> on_value (e_app_real e))

let vtv_of_expr e = match e.e_vty with
  | VTvalue vtv -> vtv
  | VTarrow _ -> raise (ValueExpected e)

let e_plapp pls el ity =
  let rec app tl vars ghost eff sbs vtvl argl =
    match vtvl, argl with
      | [],[] ->
          let vtv = pls.pl_value in
          let ghost = ghost || vtv.vtv_ghost in
          let sbs = ity_match sbs vtv.vtv_ity ity in
          let mut = Util.option_map (reg_full_inst sbs) vtv.vtv_mut in
          let vty = VTvalue (vty_value ~ghost ?mut ity) in
          let eff = eff_union eff (eff_full_inst sbs pls.pl_effect) in
          let t = match pls.pl_ls.ls_value with
            | Some _ -> fs_app pls.pl_ls tl (ty_of_ity ity)
            | None   -> ps_app pls.pl_ls tl in
          mk_expr (Elogic t) vty eff vars
      | [],_ | _,[] ->
          raise (Term.BadArity
            (pls.pl_ls, List.length pls.pl_args, List.length el))
      | vtv::vtvl, ({ e_node = Elogic t } as e)::argl ->
          let t = match t.t_ty with
            | Some _ -> t
            | None -> t_if_simp t t_bool_true t_bool_false in
          let evtv = vtv_of_expr e in
          let ghost = ghost || (evtv.vtv_ghost && not vtv.vtv_ghost) in
          let eff = eff_union eff e.e_effect in
          let sbs = ity_match sbs vtv.vtv_ity evtv.vtv_ity in
          app (t::tl) (add_e_vars e vars) ghost eff sbs vtvl argl
      | vtv::vtvl, e::argl ->
          let apply_to_pv pv =
            let t = t_var pv.pv_vs in
            let ghost = ghost || (pv.pv_vtv.vtv_ghost && not vtv.vtv_ghost) in
            let sbs = ity_match sbs vtv.vtv_ity pv.pv_vtv.vtv_ity in
            app (t::tl) (add_pv_vars pv vars) ghost eff sbs vtvl argl
          in
          on_value apply_to_pv e
  in
  let vtvl = List.rev pls.pl_args in
  let argl = List.rev el in
  app [] Mid.empty false eff_empty ity_subst_empty vtvl argl

let e_lapp ls el ity =
  let pls = {
    pl_ls     = ls;
    pl_args   = List.map (fun ty -> vty_value (ity_of_ty ty)) ls.ls_args;
    pl_value  = vty_value (ity_of_ty_opt ls.ls_value);
    pl_effect = eff_empty; }
  in
  e_plapp pls el ity

let e_void = e_lapp (fs_tuple 0) [] ity_unit

let e_if e0 e1 e2 =
  let vtv0 = vtv_of_expr e0 in
  let vtv1 = vtv_of_expr e1 in
  let vtv2 = vtv_of_expr e2 in
  ity_equal_check vtv0.vtv_ity ity_bool;
  ity_equal_check vtv1.vtv_ity vtv2.vtv_ity;
  let eff = eff_union e1.e_effect e2.e_effect in
  let vars = add_e_vars e2 (add_e_vars e1 Mid.empty) in
  let ghost = vtv0.vtv_ghost || vtv1.vtv_ghost || vtv2.vtv_ghost in
  let vty = VTvalue (vty_value ~ghost vtv1.vtv_ity) in
  let eff = if ghost then eff_ghostify eff else eff in
  check_postexpr e0 eff vars;
  let vars = add_e_vars e0 vars in
  let eff = eff_union e0.e_effect eff in
  mk_expr (Eif (e0,e1,e2)) vty eff vars

let e_case e0 bl =
  let vtv0 = vtv_of_expr e0 in
  let bity = match bl with
    | (_,e)::_ -> (vtv_of_expr e).vtv_ity
    | [] -> raise Term.EmptyCase in
  let rec branch ghost eff vars = function
    | (pp,e)::bl ->
        let vtv = vtv_of_expr e in
        if pp.ppat_vtv.vtv_mut <> None then
          Loc.errorm "Mutable pattern in a non-mutable position";
        if pp.ppat_vtv.vtv_ghost <> vtv0.vtv_ghost then
          Loc.errorm "Non-ghost pattern in a ghost position";
        ity_equal_check vtv0.vtv_ity pp.ppat_vtv.vtv_ity;
        ity_equal_check bity vtv.vtv_ity;
        let ghost = ghost || vtv.vtv_ghost in
        let del_vs vs _ m = Mid.remove vs.vs_name m in
        let bvars = Mvs.fold del_vs pp.ppat_pattern.pat_vars e.e_vars in
        let eff = eff_union (eff_union eff pp.ppat_effect) e.e_effect in
        branch ghost eff (varmap_union vars bvars) bl
    | [] ->
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = if ghost then eff_ghostify eff else eff in
        check_postexpr e0 eff vars; (* cumulated vars *)
        let eff = eff_union e0.e_effect eff in
        let vty = VTvalue (vty_value ~ghost bity) in
        mk_expr (Ecase (e0,bl)) vty eff (add_e_vars e0 vars)
  in
  branch vtv0.vtv_ghost eff_empty Mid.empty bl

exception Immutable of expr

let e_assign_real e0 pv =
  let vtv0 = vtv_of_expr e0 in
  let r = match vtv0.vtv_mut with
    | Some r -> r
    | None -> raise (Immutable e0) in
  let ghost = vtv0.vtv_ghost || pv.pv_vtv.vtv_ghost in
  let eff = eff_assign eff_empty ~ghost r pv.pv_vtv.vtv_ity in
  let vars = add_pv_vars pv Mid.empty in
  check_postexpr e0 eff vars;
  let vars = add_e_vars e0 vars in
  let eff = eff_union e0.e_effect eff in
  let vty = VTvalue (vty_value ~ghost ity_unit) in
  let e = mk_expr (Eassign (e0,r,pv)) vty eff vars in
  (* FIXME? Ok, this is awkward. We prohibit assignments
     where a ghost value is being written in a non-ghost
     mutable lvalue (which is reasonable), but we build the
     offending expression nonetheless and include it into
     the exception! But in fact, there is nothing inherently
     bad in such expressions, and the check here serves only
     to catch potential problems early. Indeed, it is quite
     easy to fool: it suffices to write (ghost r).val <- ghv,
     to put a ghost value ghv into a non-ghost reference r.
     The real check is written above in e_let, where we ensure
     that every ghost write (whether it was made into a ghost
     lvalue or not) is never followed by a non-ghost read. *)
  if not vtv0.vtv_ghost && pv.pv_vtv.vtv_ghost then
    raise (GhostWrite (e,r));
  e

let e_assign me e = on_value (e_assign_real me) e

let e_ghost e =
  mk_expr (Eghost e) (vty_ghostify e.e_vty) e.e_effect e.e_vars

let e_any tyc =
  let varm = check_c tyc in
  let vars = varmap_join varm vars_empty in
  mk_expr (Eany tyc) (build_c vars tyc) tyc.c_effect varm

let e_const t =
  let vtv = vty_value (ity_of_ty_opt t.t_ty) in
  mk_expr (Elogic t) (VTvalue vtv) eff_empty Mid.empty

let e_int_const s = e_const (t_int_const s)
let e_real_const rc = e_const (t_real_const rc)
let e_const c = e_const (t_const c)

(* FIXME? Should we rather use boolean constants here? *)
let e_true =
  mk_expr (Elogic t_true) (VTvalue (vty_value ity_bool)) eff_empty Mid.empty

let e_false =
  mk_expr (Elogic t_false) (VTvalue (vty_value ity_bool)) eff_empty Mid.empty

let on_fmla fn e = match e.e_node with
  | Elogic ({ t_ty = None } as f) -> fn e f
  | Elogic t -> fn e (t_equ_simp t t_bool_true)
  | Evalue pv -> fn e (t_equ_simp (t_var pv.pv_vs) t_bool_true)
  | _ ->
      let ld = create_let_defn (id_fresh "o") e in
      let pv = match ld.let_var with
        | LetA _ -> raise (ValueExpected e)
        | LetV pv -> pv in
      e_let ld (fn (e_value pv) (t_equ_simp (t_var pv.pv_vs) t_bool_true))

let e_not e =
  on_fmla (fun e f ->
    let vtv = vtv_of_expr e in
    ity_equal_check vtv.vtv_ity ity_bool;
    let vty = VTvalue (vty_value ~ghost:vtv.vtv_ghost ity_bool) in
    mk_expr (Elogic (t_not f)) vty e.e_effect e.e_vars) e

let e_binop op e1 e2 =
  on_fmla (fun e2 f2 -> on_fmla (fun e1 f1 ->
    let vtv1 = vtv_of_expr e1 in
    let vtv2 = vtv_of_expr e2 in
    ity_equal_check vtv1.vtv_ity ity_bool;
    ity_equal_check vtv2.vtv_ity ity_bool;
    let vars = add_e_vars e1 e2.e_vars in
    let eff = eff_union e1.e_effect e2.e_effect in
    let ghost = vtv1.vtv_ghost || vtv2.vtv_ghost in
    let vty = VTvalue (vty_value ~ghost ity_bool) in
    mk_expr (Elogic (t_binary op f1 f2)) vty eff vars) e1) e2

let e_lazy_and e1 e2 =
  if eff_is_empty e2.e_effect then e_binop Tand e1 e2 else e_if e1 e2 e_false

let e_lazy_or e1 e2 =
  if eff_is_empty e2.e_effect then e_binop Tor e1 e2 else e_if e1 e_true e2

(* FIXME? We don't call check_postexpr to verify that raising
   an exception is ok after the computation of e, because with
   the current semantics of whyml it always is. However, this
   might break some day. *)
let e_raise xs e ity =
  let vtv = vtv_of_expr e in
  ity_equal_check xs.xs_ity vtv.vtv_ity;
  let ghost = vtv.vtv_ghost in
  let eff = eff_raise e.e_effect ~ghost xs in
  let vty = VTvalue (vty_value ~ghost ity) in
  mk_expr (Eraise (xs,e)) vty eff e.e_vars

let e_try e0 bl =
  let vtv0 = vtv_of_expr e0 in
  let rec branch ghost eff vars = function
    | (xs,pv,e)::bl ->
        let vtv = vtv_of_expr e in
        ity_equal_check vtv0.vtv_ity vtv.vtv_ity;
        ity_equal_check xs.xs_ity pv.pv_vtv.vtv_ity;
        if pv.pv_vtv.vtv_mut <> None then
          Loc.errorm "Mutable variable in a try-with branch";
        (* we don't care about pv being ghost *)
        let ghost = ghost || vtv.vtv_ghost in
        let eff = eff_union eff e.e_effect in
        let bvars = Mid.remove pv.pv_vs.vs_name e.e_vars in
        branch ghost eff (varmap_union vars bvars) bl
    | [] ->
        let vty = VTvalue (vty_value ~ghost vtv0.vtv_ity) in
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = if ghost then eff_ghostify eff else eff in
        check_postexpr e0 eff vars; (* cumulated vars *)
        (* remove from e0.e_effect the catched exceptions *)
        let remove eff0 (xs,_,_) =
          (* we catch in a ghost exception in a non-ghost code *)
          if not ghost && Sexn.mem xs eff0.eff_ghostx then
            raise (GhostRaise (e0,xs));
          eff_remove_raise eff0 xs in
        let eff0 = List.fold_left remove e0.e_effect bl in
        (* total effect and vars *)
        let eff = eff_union eff0 eff in
        let vars = add_e_vars e0 vars in
        mk_expr (Etry (e0,bl)) vty eff vars
  in
  branch vtv0.vtv_ghost eff_empty Mid.empty bl

let e_absurd ity =
  let vty = VTvalue (vty_value ity) in
  mk_expr Eabsurd vty eff_empty Mid.empty

let e_assert ak f =
  let vars = add_t_vars f Mid.empty in
  let vty = VTvalue (vty_value ity_unit) in
  mk_expr (Eassert (ak, f)) vty eff_empty vars

(* Compute the fixpoint on recursive definitions *)

let vars_equal vs1 vs2 =
  Stv.equal vs1.vars_tv vs2.vars_tv &&
  Sreg.equal vs1.vars_reg vs2.vars_reg

let eff_equal eff1 eff2 =
  Sreg.equal eff1.eff_reads  eff2.eff_reads  &&
  Sreg.equal eff1.eff_writes eff2.eff_writes &&
  Sexn.equal eff1.eff_raises eff2.eff_raises &&
  Sreg.equal eff1.eff_ghostr eff2.eff_ghostr &&
  Sreg.equal eff1.eff_ghostw eff2.eff_ghostw &&
  Sexn.equal eff1.eff_ghostx eff2.eff_ghostx &&
  Mreg.equal (Util.option_eq reg_equal) eff1.eff_resets eff2.eff_resets

let vtv_equal vtv1 vtv2 =
  ity_equal vtv1.vtv_ity vtv2.vtv_ity &&
  vtv1.vtv_ghost = vtv2.vtv_ghost &&
  option_eq reg_equal vtv1.vtv_mut vtv2.vtv_mut

let rec vta_equal vta1 vta2 =
  vtv_equal vta1.vta_arg vta2.vta_arg &&
  eff_equal vta1.vta_effect vta2.vta_effect &&
  vta1.vta_ghost = vta2.vta_ghost &&
  match vta1.vta_result, vta2.vta_result with
    | VTvalue vtv1, VTvalue vtv2 -> vtv_equal vtv1 vtv2
    | VTarrow vta1, VTarrow vta2 -> vta_equal vta1 vta2
    | _, _ -> false

let ps_compat ps1 ps2 =
  vta_equal ps1.ps_vta ps2.ps_vta &&
  vars_equal ps1.ps_vars ps2.ps_vars

let rec expr_subst psm e = match e.e_node with
  | Earrow ps when Mid.mem ps.ps_name psm ->
      e_cast (Mid.find ps.ps_name psm) e.e_vty
  | Eapp (e,pv) ->
      e_app_real (expr_subst psm e) pv
  | Elet ({ let_var = LetV pv ; let_expr = d }, e) ->
      let nd = expr_subst psm d in
      let vtv = match nd.e_vty with VTvalue vtv -> vtv | _ -> assert false in
      if not (vtv_equal vtv pv.pv_vtv) then Loc.errorm "vty_value mismatch";
      e_let { let_var = LetV pv ; let_expr = nd } (expr_subst psm e)
  | Elet ({ let_var = LetA ps ; let_expr = d }, e) ->
      let ld = create_let_defn (id_clone ps.ps_name) (expr_subst psm d) in
      let ns = match ld.let_var with LetA a -> a | LetV _ -> assert false in
      e_let ld (expr_subst (Mid.add ps.ps_name ns psm) e)
  | Erec (rdl,e) ->
      let conv lam = { lam with l_expr = expr_subst psm lam.l_expr } in
      let defl = List.map (fun rd -> rd.rec_ps, conv rd.rec_lambda) rdl in
      let rdl = create_rec_defn defl in
      let add psm (ps,_) rd = Mid.add ps.ps_name rd.rec_ps psm in
      e_rec rdl (expr_subst (List.fold_left2 add psm defl rdl) e)
  | Eif (e,e1,e2) ->
      e_if (expr_subst psm e) (expr_subst psm e1) (expr_subst psm e2)
  | Ecase (e,bl) ->
      let branch (pp,e) = pp, expr_subst psm e in
      e_case (expr_subst psm e) (List.map branch bl)
  | Eassign (e,_,pv) ->
      e_assign_real (expr_subst psm e) pv
  | Eghost e ->
      e_ghost (expr_subst psm e)
  | Eraise (xs,e0) ->
      e_raise xs (expr_subst psm e0) (vtv_of_expr e).vtv_ity
  | Etry (e,bl) ->
      let branch (xs,pv,e) = xs, pv, expr_subst psm e in
      e_try (expr_subst psm e) (List.map branch bl)
  | Elogic _ | Evalue _ | Earrow _ | Eany _ | Eabsurd | Eassert _ -> e

and create_rec_defn defl =
  let conv m (ps,lam) =
    let rd = create_fun_defn (id_clone ps.ps_name) lam in
    if ps_compat ps rd.rec_ps then m, { rd with rec_ps = ps }
    else Mid.add ps.ps_name rd.rec_ps m, rd in
  let m, defl = Util.map_fold_left conv Mid.empty defl in
  let subst { rec_ps = ps ; rec_lambda = lam } =
    let lam = { lam with l_expr = expr_subst m lam.l_expr } in
    Mid.find_def ps ps.ps_name m, lam in
  if Mid.is_empty m then defl else
  create_rec_defn (List.map subst defl)

let create_fun_defn id lam =
  if lam.l_variant <> [] then
    Loc.errorm "Variants are not allowed in a non-recursive definition";
  create_fun_defn id lam

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

