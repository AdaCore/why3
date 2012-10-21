(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Util
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T

(** program/logic symbols *)

type plsymbol = {
  pl_ls     : lsymbol;
  pl_args   : vty_value list;
  pl_value  : vty_value;
  pl_effect : effect;
  pl_hidden : bool;
  pl_rdonly : bool;
}

let pl_equal : plsymbol -> plsymbol -> bool = (==)

let create_plsymbol_unsafe, restore_pl =
  let ls_to_pls = Wls.create 17 in
  (fun ls args value effect ~hidden ~rdonly ->
    let pl = {
      pl_ls     = ls;
      pl_args   = args;
      pl_value  = value;
      pl_effect = effect;
      pl_hidden = hidden;
      pl_rdonly = rdonly;
    } in
    Wls.set ls_to_pls ls pl;
    pl),
  Wls.find ls_to_pls

let create_plsymbol ?(hidden=false) ?(rdonly=false) id args value =
  let ty_of_vtv vtv = ty_of_ity vtv.vtv_ity in
  let pure_args = List.map ty_of_vtv args in
  let ls = create_fsymbol id pure_args (ty_of_vtv value) in
  let eff_read e r = eff_read e ~ghost:value.vtv_ghost r in
  let effect = Opt.fold eff_read eff_empty value.vtv_mut in
  let arg_reset acc a = Opt.fold eff_reset acc a.vtv_mut in
  let effect = List.fold_left arg_reset effect args in
  create_plsymbol_unsafe ls args value effect ~hidden ~rdonly

let ity_of_ty_opt ty = ity_of_ty (Opt.get_def ty_bool ty)

let fake_pls = Wls.memoize 17 (fun ls ->
  { pl_ls     = ls;
    pl_args   = List.map (fun ty -> vty_value (ity_of_ty ty)) ls.ls_args;
    pl_value  = vty_value (ity_of_ty_opt ls.ls_value);
    pl_effect = eff_empty;
    pl_hidden = false;
    pl_rdonly = false; })

exception HiddenPLS of lsymbol
exception RdOnlyPLS of lsymbol

(** cloning *)

type symbol_map = {
  sm_pure : Theory.symbol_map;
  sm_its  : itysymbol Mits.t;
  sm_pls  : plsymbol Mls.t;
}

let pl_clone sm =
  let itsm, regm = its_clone sm in
  let conv_reg r = Mreg.find r regm in
  let conv_its its = Mits.find_def its its itsm in
  let conv_ts ts = Mts.find_def ts ts sm.Theory.sm_ts in
  let rec conv_ity ity = match ity.ity_node with
    | Ityapp (its,tl,rl) ->
        let tl = List.map conv_ity tl in
        let rl = List.map conv_reg rl in
        ity_app (conv_its its) tl rl
    | Itypur (ts,tl) ->
        let tl = List.map conv_ity tl in
        ity_pur (conv_ts ts) tl
    | Ityvar _ -> ity
  in
  let conv_vtv v =
    let ghost = v.vtv_ghost in
    let mut, ity = match v.vtv_mut with
      | Some r -> let r = conv_reg r in Some r, r.reg_ity
      | None   -> None, conv_ity v.vtv_ity in
    vty_value ~ghost ?mut ity
  in
  let conv_eff eff =
    let e = eff_empty in
    assert (Sexn.is_empty eff.eff_raises);
    assert (Sexn.is_empty eff.eff_ghostx);
    let conv ghost r e = eff_read ~ghost e (conv_reg r) in
    let e = Sreg.fold (conv false) eff.eff_reads  e in
    let e = Sreg.fold (conv true)  eff.eff_ghostr e in
    let conv ghost r e = eff_write ~ghost e (conv_reg r) in
    let e = Sreg.fold (conv false) eff.eff_writes e in
    let e = Sreg.fold (conv true)  eff.eff_ghostw e in
    let conv r u e = match u with
      | Some u -> eff_refresh e (conv_reg r) (conv_reg u)
      | None   -> eff_reset e (conv_reg r) in
    Mreg.fold conv eff.eff_resets e
  in
  let add_pl opls nls acc =
    let npls = try restore_pl nls with Not_found ->
      let args = List.map conv_vtv opls.pl_args in
      let value = conv_vtv opls.pl_value in
      let effect = conv_eff opls.pl_effect in
      let hidden = opls.pl_hidden in
      let rdonly = opls.pl_rdonly in
      create_plsymbol_unsafe nls args value effect ~hidden ~rdonly
    in
    Mls.add opls.pl_ls npls acc
  in
  let add_ls ols nls acc =
    try add_pl (restore_pl ols) nls acc with Not_found -> acc
  in
  let plsm = Mls.fold add_ls sm.Theory.sm_ls Mls.empty in
  { sm_pure = sm;
    sm_its  = itsm;
    sm_pls  = plsm; }

(** patterns *)

type ppattern = {
  ppat_pattern : pattern;
  ppat_vtv     : vty_value;
  ppat_effect  : effect;
}

let ppat_is_wild pp = match pp.ppat_pattern.pat_node with
  | Pwild -> true
  | _ -> false

let ppat_wild vtv =
  if vtv.vtv_mut <> None then Loc.errorm "Wildcard patterns are immutable";
  { ppat_pattern = pat_wild (ty_of_ity vtv.vtv_ity);
    ppat_vtv     = vtv;
    ppat_effect  = eff_empty; }

let ppat_var pv =
  { ppat_pattern = pat_var pv.pv_vs;
    ppat_vtv     = pv.pv_vtv;
    ppat_effect  = eff_empty; }

let ppat_plapp pls ppl vtv =
  if vtv.vtv_mut <> None then
    Loc.errorm "Only variable patterns can be mutable";
  if pls.pl_hidden then raise (HiddenPLS pls.pl_ls);
  let sbs = ity_match ity_subst_empty pls.pl_value.vtv_ity vtv.vtv_ity in
  let mtch eff arg pp =
    ignore (ity_match sbs arg.vtv_ity pp.ppat_vtv.vtv_ity);
    let ghost = pp.ppat_vtv.vtv_ghost in
    if ghost <> (vtv.vtv_ghost || arg.vtv_ghost) then
      Loc.errorm "Ghost pattern in a non-ghost context";
    let effect = eff_union eff pp.ppat_effect in
    let arg_mut = if pls.pl_rdonly then None else arg.vtv_mut in
    match arg_mut, pp.ppat_vtv.vtv_mut with
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
  let eff = try List.fold_left2 mtch eff_empty pls.pl_args ppl with
    | Not_found -> raise (Pattern.ConstructorExpected pls.pl_ls)
    | Invalid_argument _ -> raise (Term.BadArity
        (pls.pl_ls, List.length pls.pl_args, List.length ppl)) in
  let pl = List.map (fun pp -> pp.ppat_pattern) ppl in
  { ppat_pattern = pat_app pls.pl_ls pl (ty_of_ity vtv.vtv_ity);
    ppat_vtv     = vtv;
    ppat_effect  = if vtv.vtv_ghost then eff_ghostify eff else eff; }

let ppat_lapp ls ppl vtv = ppat_plapp (fake_pls ls) ppl vtv

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
  let hv = Hstr.create 3 in
  let find id vtv =
    let nm = preid_name id in
    try
      let pv = Hstr.find hv nm in
      ity_equal_check vtv.vtv_ity pv.pv_vtv.vtv_ity;
      pv
    with Not_found ->
      let pv = create_pvsymbol id vtv in
      Hstr.add hv nm pv; pv
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
        if pls.pl_hidden then raise (HiddenPLS pls.pl_ls);
        let sbs = ity_match ity_subst_empty pls.pl_value.vtv_ity vtv.vtv_ity in
        let mtch arg pp =
          let ity = ity_full_inst sbs arg.vtv_ity in
          let ghost = vtv.vtv_ghost || arg.vtv_ghost in
          let arg_mut = if pls.pl_rdonly then None else arg.vtv_mut in
          let mut = Opt.map (reg_full_inst sbs) arg_mut in
          let pp = make (vty_value ~ghost ?mut ity) pp in
          if ppat_is_wild pp then pp.ppat_effect, pp else
          Opt.fold (eff_read ~ghost) pp.ppat_effect mut, pp
        in
        let ppl = try List.map2 mtch pls.pl_args ppl with
          | Not_found -> raise (Pattern.ConstructorExpected pls.pl_ls)
          | Invalid_argument _ -> raise (Term.BadArity
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
        let ppl = try List.map2 mtch ls.ls_args ppl with
          | Not_found -> raise (Pattern.ConstructorExpected ls)
          | Invalid_argument _ -> raise (Term.BadArity
              (ls,List.length ls.ls_args,List.length ppl)) in
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
  Hstr.fold Mstr.add hv Mstr.empty, pp

(** program symbols *)

type psymbol = {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_varm  : varmap;
  ps_vars  : varset;
  ps_subst : ity_subst;
}

module Psym = WeakStructMake (struct
  type t = psymbol
  let tag ps = ps.ps_name.id_tag
end)

module Sps = Psym.S
module Mps = Psym.M
module Hps = Psym.H
module Wps = Psym.W

let ps_equal : psymbol -> psymbol -> bool = (==)

let create_psymbol_real ~poly id vta varm =
  let vars = if poly then vars_empty else vta_vars vta in
  let vars = vars_merge varm vars in
  { ps_name  = id_register id;
    ps_vta   = vta_filter varm vta;
    ps_varm  = varm;
    ps_vars  = vars;
    ps_subst = vars_freeze vars; }

let create_psymbol_poly = create_psymbol_real ~poly:true
let create_psymbol_mono = create_psymbol_real ~poly:false

(** specification *)

let varmap_union = Mid.set_union

let add_pv_vars pv m = Mid.add pv.pv_vs.vs_name pv.pv_vars m
let add_vs_vars vs _ m = add_pv_vars (restore_pv vs) m
let add_t_vars vss m = Mvs.fold add_vs_vars vss m

let add_ps_vars ps m =
  Mid.add ps.ps_name ps.ps_vars (varmap_union ps.ps_varm m)

let pre_vars f vsset = Mvs.set_union vsset f.t_vars
let post_vars f vsset = Mvs.set_union vsset f.t_vars
let xpost_vars = Mexn.fold (fun _ -> post_vars)

let variant_vars varl vsset =
  let add_variant s (t,_) = Mvs.set_union s t.t_vars in
  List.fold_left add_variant vsset varl

let spec_vsset spec =
  let vsset = pre_vars spec.c_pre Mvs.empty in
  let vsset = post_vars spec.c_post vsset in
  let vsset = xpost_vars spec.c_xpost vsset in
  let vsset = variant_vars spec.c_variant vsset in
  vsset

let spec_varmap varm spec = add_t_vars (spec_vsset spec) varm

let spec_pvset pvs spec =
  let add_vs vs _ s = Spv.add (restore_pv vs) s in
  Mvs.fold add_vs (spec_vsset spec) pvs

let rec vta_varmap vta =
  let varm = match vta.vta_result with
    | VTarrow a -> vta_varmap a
    | VTvalue _ -> Mid.empty in
  let varm = spec_varmap varm vta.vta_spec in
  let del_pv m pv = Mid.remove pv.pv_vs.vs_name m in
  List.fold_left del_pv varm vta.vta_args

let eff_check vars result e =
  let check vars r = if not (reg_occurs r vars) then
    Loc.errorm "every external effect must be mentioned in specification" in
  let reset vars r u = check vars r; Opt.iter (check vars) u in
  let check = check vars in
  Sreg.iter check e.eff_reads;
  Sreg.iter check e.eff_writes;
  Sreg.iter check e.eff_ghostr;
  Sreg.iter check e.eff_ghostw;
  if not (Mreg.is_empty e.eff_resets) then
    let reset = reset (vars_union vars (vty_vars result)) in
    Mreg.iter reset e.eff_resets

let vtv_check vars eff vtv =
  let on_reg r =
    if not (reg_occurs r vars) &&
      (try Mreg.find r eff.eff_resets <> None with Not_found -> true)
    then Loc.errorm "every fresh region in the result must be reset" in
  reg_iter on_reg vtv.vtv_ity.ity_vars

let rec vta_check vars vta =
  let add_arg vars pv = vars_union vars pv.pv_vars in
  let vars = List.fold_left add_arg vars vta.vta_args in
  eff_check vars vta.vta_result vta.vta_spec.c_effect;
  if vta.vta_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.vta_check";
  match vta.vta_result with
  | VTarrow a -> vta_check vars a
  | VTvalue v -> vtv_check vars vta.vta_spec.c_effect v

let create_psymbol id vta =
  let ps = create_psymbol_poly id vta (vta_varmap vta) in
  vta_check ps.ps_vars vta;
  ps

let create_psymbol_extra id vta pvs pss =
  let varm = vta_varmap vta in
  let varm = Spv.fold add_pv_vars pvs varm in
  let varm = Sps.fold add_ps_vars pss varm in
  let ps = create_psymbol_poly id vta varm in
  vta_check ps.ps_vars vta;
  ps

(** program expressions *)

type assertion_kind = Aassert | Aassume | Acheck

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type let_sym =
  | LetV of pvsymbol
  | LetA of psymbol

type expr = {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_varm   : varmap;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Elogic  of term
  | Evalue  of pvsymbol
  | Earrow  of psymbol
  | Eapp    of expr * pvsymbol * spec
  | Elet    of let_defn * expr
  | Erec    of fun_defn list * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (ppattern * expr) list
  | Eassign of expr * region * pvsymbol
  | Eghost  of expr
  | Eany    of spec
  | Eloop   of invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
  | Eraise  of xsymbol * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eabstr  of expr * spec
  | Eassert of assertion_kind * term
  | Eabsurd

and let_defn = {
  let_sym  : let_sym;
  let_expr : expr;
}

and fun_defn = {
  fun_ps     : psymbol;
  fun_lambda : lambda;
  fun_varm   : varmap;
}

and lambda = {
  l_args : pvsymbol list;
  l_expr : expr;
  l_spec : spec;
}

(* base tools *)

let e_label ?loc l e = { e with e_label = l; e_loc = loc }

let e_label_add l e = { e with e_label = Slab.add l e.e_label }

let e_label_copy { e_label = lab; e_loc = loc } e =
  let lab = Slab.union lab e.e_label in
  let loc = if e.e_loc = None then loc else e.e_loc in
  { e with e_label = lab; e_loc = loc }

exception ValueExpected of expr
exception ArrowExpected of expr

let vtv_of_expr e = match e.e_vty with
  | VTvalue vtv -> vtv
  | VTarrow _ -> Loc.error ?loc:e.e_loc (ValueExpected e)

let vta_of_expr e = match e.e_vty with
  | VTvalue _ -> Loc.error ?loc:e.e_loc (ArrowExpected e)
  | VTarrow vta -> vta

let pv_effect pv = match pv.pv_vtv.vtv_mut with
  | Some r -> eff_read ~ghost:pv.pv_vtv.vtv_ghost eff_empty r
  | None -> eff_empty

let add_e_vars e m = varmap_union e.e_varm m

let varmap_pvset pvs varm =
  let add_id id _ s =
    try Spv.add (restore_pv_by_id id) s
    with Not_found -> s in
  Mid.fold add_id varm pvs

let ps_pvset pvs ps = varmap_pvset pvs ps.ps_varm

let e_pvset pvs e = varmap_pvset pvs e.e_varm

let l_pvset pvs lam =
  let pvs = e_pvset pvs lam.l_expr in
  let pvs = spec_pvset pvs lam.l_spec in
  List.fold_right Spv.remove lam.l_args pvs

(* check admissibility of consecutive events *)

exception StaleRegion of expr * ident
exception GhostWrite of expr * region
exception GhostRaise of expr * xsymbol

let check_reset e varm =
  (* If we reset a region, then it may only occur in the later code
     as the result of the resetting expression. Otherwise, this is
     a freshness violation: some symbol defined earlier carries that
     region into the later code. *)
  let check_id id vars = if eff_stale_region e.e_effect vars then
    Loc.error ?loc:e.e_loc (StaleRegion (e,id)) in
  if not (Mreg.is_empty e.e_effect.eff_resets) then
    Mid.iter check_id varm

let check_ghost_write e eff =
  (* If we make a ghost write, then the modified region cannot
     be read in a later non-ghost code. We ignore any resets:
     a once ghostified region must stay so, even if it is reset. *)
  let badwr = Sreg.inter e.e_effect.eff_ghostw eff.eff_reads in
  if not (Sreg.is_empty badwr) then
    Loc.error ?loc:e.e_loc (GhostWrite (e, Sreg.choose badwr))

let check_postexpr e eff varm =
  check_ghost_write e eff;
  check_reset e varm

(* smart constructors *)

let mk_expr node vty eff varm = {
  e_node   = node;
  e_vty    = vty;
  e_effect = if vty_ghost vty then eff_ghostify eff else eff;
  e_varm   = varm;
  e_label  = Slab.empty;
  e_loc    = None;
}

(* program variables and program symbols *)

let e_value pv =
  let varm = add_pv_vars pv Mid.empty in
  mk_expr (Evalue pv) (VTvalue pv.pv_vtv) (pv_effect pv) varm

let e_arrow ps vta =
  let varm = add_ps_vars ps Mid.empty in
  let sbs = vta_vars_match ps.ps_subst ps.ps_vta vta in
  let vta = vta_full_inst sbs ps.ps_vta in
  mk_expr (Earrow ps) (VTarrow vta) eff_empty varm

(* let-definitions *)

let create_let_defn id e =
  let lv = match e.e_vty with
    | VTvalue vtv ->
        LetV (create_pvsymbol id (vtv_unmut vtv))
    | VTarrow vta ->
        LetA (create_psymbol_mono id vta e.e_varm)
  in
  { let_sym = lv ; let_expr = e }

let e_let ({ let_sym = lv ; let_expr = d } as ld) e =
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA ps -> ps.ps_name in
  let varm = Mid.remove id e.e_varm in
  check_postexpr d e.e_effect varm;
  let eff = eff_union d.e_effect e.e_effect in
  mk_expr (Elet (ld,e)) e.e_vty eff (add_e_vars d varm)

let on_value fn e = match e.e_node with
  | Evalue pv -> fn pv
  | _ ->
      let id = id_fresh ?loc:e.e_loc "o" in
      let ld = create_let_defn id e in
      let pv = match ld.let_sym with
        | LetA _ -> Loc.error ?loc:e.e_loc (ValueExpected e)
        | LetV pv -> pv in
      e_let ld (fn pv)

(* application *)

let e_app_real e pv =
  let spec,vty = vta_app (vta_of_expr e) pv in
  check_postexpr e spec.c_effect (add_pv_vars pv Mid.empty);
  let eff = eff_union e.e_effect spec.c_effect in
  let eff = eff_union eff (pv_effect pv) in
  mk_expr (Eapp (e,pv,spec)) vty eff (add_pv_vars pv e.e_varm)

let rec e_app_flatten e pv = match e.e_node with
  (* TODO/FIXME? here, we avoid capture in the first case,
     but such an expression would break WP anyway. Though
     it cannot come from a parsed WhyML program where the
     typing ensures the uniqueness of pvsymbols, one can
     construct it using the API directly. *)
  | Elet ({ let_sym = LetV pv' }, _) when pv_equal pv pv' -> e_app_real e pv
  | Elet (ld, e) -> e_let ld (e_app_flatten e pv)
  | _ -> e_app_real e pv

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

let e_app = List.fold_left (fun e -> on_value (e_app_flatten e))

let e_plapp pls el ity =
  if pls.pl_hidden then raise (HiddenPLS pls.pl_ls);
  if pls.pl_rdonly then raise (RdOnlyPLS pls.pl_ls);
  let rec app tl varm ghost eff sbs vtvl argl =
    match vtvl, argl with
      | [],[] ->
          let vtv = pls.pl_value in
          let ghost = ghost || vtv.vtv_ghost in
          let sbs = ity_match sbs vtv.vtv_ity ity in
          let mut = match pls.pl_args with
            (* if our sole argument is a private type, then we are immutable *)
            | [{vtv_ity = {ity_node = Ityapp ({its_priv = true},_,_)}}] -> None
            | _ -> vtv.vtv_mut in
          let mut = Opt.map (reg_full_inst sbs) mut in
          let vty = VTvalue (vty_value ~ghost ?mut ity) in
          let eff = eff_union eff (eff_full_inst sbs pls.pl_effect) in
          let t = match pls.pl_ls.ls_value with
            | Some _ -> fs_app pls.pl_ls tl (ty_of_ity ity)
            | None   -> ps_app pls.pl_ls tl in
          mk_expr (Elogic t) vty eff varm
      | [],_ | _,[] ->
          raise (Term.BadArity
            (pls.pl_ls, List.length pls.pl_args, List.length el))
      | vtv::vtvl, ({ e_node = Elogic t } as e)::argl ->
          let t = match t.t_ty with
            | Some _ -> t
            | None -> t_if_simp t t_bool_true t_bool_false in
          let evtv = vtv_of_expr e in
          let ghost = ghost || (evtv.vtv_ghost && not vtv.vtv_ghost) in
          if vtv.vtv_ghost && not evtv.vtv_ghost then
            Loc.errorm "non-ghost value passed as a ghost argument";
          let eff = eff_union eff e.e_effect in
          let sbs = ity_match sbs vtv.vtv_ity evtv.vtv_ity in
          app (t::tl) (add_e_vars e varm) ghost eff sbs vtvl argl
      | vtv::vtvl, e::argl ->
          let apply_to_pv pv =
            let t = t_var pv.pv_vs in
            let eff = eff_union eff (pv_effect pv) in
            let ghost = ghost || (pv.pv_vtv.vtv_ghost && not vtv.vtv_ghost) in
            let sbs = ity_match sbs vtv.vtv_ity pv.pv_vtv.vtv_ity in
            app (t::tl) (add_pv_vars pv varm) ghost eff sbs vtvl argl
          in
          if vtv.vtv_ghost && not (vty_ghost e.e_vty) then
            Loc.errorm "non-ghost value passed as a ghost argument";
          on_value apply_to_pv e
  in
  let vtvl = List.rev pls.pl_args in
  let argl = List.rev el in
  app [] Mid.empty false eff_empty ity_subst_empty vtvl argl

let e_lapp ls el ity = e_plapp (fake_pls ls) el ity

let fs_void = fs_tuple 0
let t_void = fs_app fs_void [] ty_unit
let e_void = e_lapp fs_void [] ity_unit

(* if and match *)

let e_if e0 e1 e2 =
  let vtv0 = vtv_of_expr e0 in
  let vtv1 = vtv_of_expr e1 in
  let vtv2 = vtv_of_expr e2 in
  ity_equal_check vtv0.vtv_ity ity_bool;
  ity_equal_check vtv1.vtv_ity vtv2.vtv_ity;
  let eff = eff_union e1.e_effect e2.e_effect in
  let varm = add_e_vars e2 (add_e_vars e1 Mid.empty) in
  let ghost = vtv0.vtv_ghost || vtv1.vtv_ghost || vtv2.vtv_ghost in
  let vty = VTvalue (vty_value ~ghost vtv1.vtv_ity) in
  let eff = if ghost then eff_ghostify eff else eff in
  check_postexpr e0 eff varm;
  let varm = add_e_vars e0 varm in
  let eff = eff_union e0.e_effect eff in
  mk_expr (Eif (e0,e1,e2)) vty eff varm

let e_case e0 bl =
  let vtv0 = vtv_of_expr e0 in
  let bity = match bl with
    | (_,e)::_ -> (vtv_of_expr e).vtv_ity
    | [] -> raise Term.EmptyCase in
  let rec branch ghost eff varm = function
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
        let bvarm = Mvs.fold del_vs pp.ppat_pattern.pat_vars e.e_varm in
        let eff = eff_union (eff_union eff pp.ppat_effect) e.e_effect in
        branch ghost eff (varmap_union varm bvarm) bl
    | [] ->
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = if ghost then eff_ghostify eff else eff in
        check_postexpr e0 eff varm; (* cumulated varmap *)
        let eff = eff_union e0.e_effect eff in
        let vty = VTvalue (vty_value ~ghost bity) in
        mk_expr (Ecase (e0,bl)) vty eff (add_e_vars e0 varm)
  in
  branch vtv0.vtv_ghost eff_empty Mid.empty bl

(* ghost *)

let e_ghost e =
  mk_expr (Eghost e) (vty_ghostify e.e_vty) e.e_effect e.e_varm

(* assignment *)

exception Immutable of expr

let e_assign_real e0 pv =
  let vtv0 = vtv_of_expr e0 in
  let r = match vtv0.vtv_mut with
    | Some r -> r
    | None -> Loc.error ?loc:e0.e_loc (Immutable e0) in
  let ghost = vtv0.vtv_ghost || pv.pv_vtv.vtv_ghost in
  let eff = eff_assign eff_empty ~ghost r pv.pv_vtv.vtv_ity in
  let varm = add_pv_vars pv Mid.empty in
  check_postexpr e0 eff varm;
  let varm = add_e_vars e0 varm in
  let eff = eff_union eff e0.e_effect in
  let eff = eff_union eff (pv_effect pv) in
  let vty = VTvalue (vty_value ~ghost ity_unit) in
  let e = mk_expr (Eassign (e0,r,pv)) vty eff varm in
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
    Loc.error (GhostWrite (e,r));
  e

let e_assign me e = on_value (e_assign_real me) e

(* numeric constants *)

let e_const t =
  let vtv = vty_value (ity_of_ty_opt t.t_ty) in
  mk_expr (Elogic t) (VTvalue vtv) eff_empty Mid.empty

let e_int_const s = e_const (t_int_const s)
let e_real_const rc = e_const (t_real_const rc)
let e_const c = e_const (t_const c)

(* boolean expressions *)

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
      let id = id_fresh ?loc:e.e_loc "o" in
      let ld = create_let_defn id e in
      let pv = match ld.let_sym with
        | LetA _ -> Loc.error ?loc:e.e_loc (ValueExpected e)
        | LetV pv -> pv in
      e_let ld (fn (e_value pv) (t_equ_simp (t_var pv.pv_vs) t_bool_true))

let e_not e =
  on_fmla (fun e f ->
    let vtv = vtv_of_expr e in
    ity_equal_check vtv.vtv_ity ity_bool;
    let vty = VTvalue (vty_value ~ghost:vtv.vtv_ghost ity_bool) in
    mk_expr (Elogic (t_not f)) vty e.e_effect e.e_varm) e

let e_binop op e1 e2 =
  on_fmla (fun e2 f2 -> on_fmla (fun e1 f1 ->
    let vtv1 = vtv_of_expr e1 in
    let vtv2 = vtv_of_expr e2 in
    ity_equal_check vtv1.vtv_ity ity_bool;
    ity_equal_check vtv2.vtv_ity ity_bool;
    let varm = add_e_vars e1 e2.e_varm in
    let eff = eff_union e1.e_effect e2.e_effect in
    let ghost = vtv1.vtv_ghost || vtv2.vtv_ghost in
    let vty = VTvalue (vty_value ~ghost ity_bool) in
    mk_expr (Elogic (t_binary op f1 f2)) vty eff varm) e1) e2

let e_lazy_and e1 e2 =
  if eff_is_empty e2.e_effect then e_binop Tand e1 e2 else e_if e1 e2 e_false

let e_lazy_or e1 e2 =
  if eff_is_empty e2.e_effect then e_binop Tor e1 e2 else e_if e1 e_true e2

(* loops *)

let e_loop inv variant e =
  let vtv = vtv_of_expr e in
  ity_equal_check vtv.vtv_ity ity_unit;
  let vsset = pre_vars inv Mvs.empty in
  let vsset = variant_vars variant vsset in
  let varm = add_t_vars vsset e.e_varm in
  check_postexpr e e.e_effect varm;
  let vty = VTvalue (vtv_unmut vtv) in
  mk_expr (Eloop (inv,variant,e)) vty e.e_effect varm

let e_for_real pv bounds inv e =
  let vtv = vtv_of_expr e in
  let pvfrom,_,pvto = bounds in
  ity_equal_check vtv.vtv_ity ity_unit;
  ity_equal_check pv.pv_vtv.vtv_ity ity_int;
  ity_equal_check pvfrom.pv_vtv.vtv_ity ity_int;
  ity_equal_check pvto.pv_vtv.vtv_ity ity_int;
  if pv.pv_vtv.vtv_mut <> None then
    Loc.errorm "mutable index in a for loop";
  let ghost = pv.pv_vtv.vtv_ghost || pvfrom.pv_vtv.vtv_ghost ||
    pvto.pv_vtv.vtv_ghost || vtv.vtv_ghost in
  let eff = if ghost then eff_ghostify e.e_effect else e.e_effect in
  let varm = add_t_vars inv.t_vars e.e_varm in
  (* FIXME? We check that no variable in the loop body, _including_
     the index variable, is not invalidated because of a region reset.
     We ignore the loop bounds, since they are computed just once. *)
  check_postexpr e eff varm;
  let varm = Mid.remove pv.pv_vs.vs_name varm in
  let varm = add_pv_vars pvfrom (add_pv_vars pvto varm) in
  let vty = VTvalue (vty_value ~ghost ity_unit) in
  mk_expr (Efor (pv,bounds,inv,e)) vty eff varm

let e_for pv efrom dir eto inv e =
  let apply pvto pvfrom = e_for_real pv (pvfrom,dir,pvto) inv e in
  let apply pvto = on_value (apply pvto) efrom in
  on_value apply eto

(* raise and try *)

let e_raise xs e ity =
  let vtv = vtv_of_expr e in
  let ghost = vtv.vtv_ghost in
  ity_equal_check xs.xs_ity vtv.vtv_ity;
  let eff = eff_raise eff_empty ~ghost xs in
  let vty = VTvalue (vty_value ~ghost ity) in
  check_postexpr e eff Mid.empty;
  let eff = eff_union eff e.e_effect in
  mk_expr (Eraise (xs,e)) vty eff e.e_varm

let e_try e0 bl =
  let vtv0 = vtv_of_expr e0 in
  let rec branch ghost eff varm = function
    | (xs,pv,e)::bl ->
        let vtv = vtv_of_expr e in
        ity_equal_check vtv0.vtv_ity vtv.vtv_ity;
        ity_equal_check xs.xs_ity pv.pv_vtv.vtv_ity;
        if pv.pv_vtv.vtv_mut <> None then
          Loc.errorm "Mutable variable in a try-with branch";
        (* we don't care about pv being ghost *)
        let ghost = ghost || vtv.vtv_ghost in
        let eff = eff_union eff e.e_effect in
        let bvarm = Mid.remove pv.pv_vs.vs_name e.e_varm in
        branch ghost eff (varmap_union varm bvarm) bl
    | [] ->
        let vty = VTvalue (vty_value ~ghost vtv0.vtv_ity) in
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = if ghost then eff_ghostify eff else eff in
        check_postexpr e0 eff varm; (* cumulated varmap *)
        (* remove from e0.e_effect the catched exceptions *)
        let remove eff0 (xs,_,_) =
          (* we catch in a ghost exception in a non-ghost code *)
          if not ghost && Sexn.mem xs eff0.eff_ghostx then
            Loc.error ?loc:e0.e_loc (GhostRaise (e0,xs));
          eff_remove_raise eff0 xs in
        let eff0 = List.fold_left remove e0.e_effect bl in
        (* total effect and varmap *)
        let eff = eff_union eff0 eff in
        let varm = add_e_vars e0 varm in
        mk_expr (Etry (e0,bl)) vty eff varm
  in
  branch vtv0.vtv_ghost eff_empty Mid.empty bl

(* specification-related expressions *)

let pv_dummy = create_pvsymbol (id_fresh "dummy") (vty_value ity_unit)

let e_any spec vty =
  if spec.c_letrec <> 0 then invalid_arg "Mlw_expr.e_any";
  let vta = vty_arrow [pv_dummy] ~spec vty in
  let varm = vta_varmap vta in
  vta_check (vars_merge varm vars_empty) vta;
  mk_expr (Eany spec) vty spec.c_effect varm

let e_abstract e spec =
  if spec.c_letrec <> 0 then invalid_arg "Mlw_expr.e_abstract";
  spec_check { spec with c_effect = e.e_effect } e.e_vty;
  let varm = spec_varmap e.e_varm spec in
  mk_expr (Eabstr (e,spec)) e.e_vty e.e_effect varm

let e_assert ak f =
  let varm = add_t_vars f.t_vars Mid.empty in
  let vty = VTvalue (vty_value ity_unit) in
  mk_expr (Eassert (ak, f)) vty eff_empty varm

let e_absurd ity =
  let vty = VTvalue (vty_value ity) in
  mk_expr Eabsurd vty eff_empty Mid.empty

(* simple functional definitions *)

let create_fun_defn id lam recsyms =
  let spec = { lam.l_spec with c_effect = lam.l_expr.e_effect } in
  let varm = spec_varmap lam.l_expr.e_varm spec in
  let del_pv m pv = Mid.remove pv.pv_vs.vs_name m in
  let varm = List.fold_left del_pv varm lam.l_args in
  let varm_ps = Mid.set_diff varm recsyms in
  let vty = match lam.l_expr.e_vty with
    | VTvalue ({ vtv_mut = Some _ } as vtv) -> VTvalue (vtv_unmut vtv)
    | vty -> vty in
  let vta = vty_arrow lam.l_args ~spec vty in
  { fun_ps     = create_psymbol_poly id vta varm_ps;
    fun_lambda = lam;
    fun_varm   = varm; }

let rec_varmap varm fdl =
  let fd, rest = match fdl with
    | [] -> invalid_arg "Mlw_expr.rec_varm"
    | fd :: fdl -> fd, fdl in
  let lr = fd.fun_ps.ps_vta.vta_spec.c_letrec in
  let bad fd = fd.fun_ps.ps_vta.vta_spec.c_letrec <> lr in
  if List.exists bad rest then invalid_arg "Mlw_expr.rec_varm";
  let add_fd m fd = varmap_union fd.fun_varm m in
  let del_fd m fd = Mid.remove fd.fun_ps.ps_name m in
  let varm = List.fold_left add_fd varm fdl in
  let varm = List.fold_left del_fd varm fdl in
  varm

let e_rec fdl e =
  let varm = rec_varmap e.e_varm fdl in
  mk_expr (Erec (fdl,e)) e.e_vty e.e_effect varm

(* compute the fixpoint on recursive definitions *)

let eff_equal eff1 eff2 =
  Sreg.equal eff1.eff_reads  eff2.eff_reads  &&
  Sreg.equal eff1.eff_writes eff2.eff_writes &&
  Sexn.equal eff1.eff_raises eff2.eff_raises &&
  Sreg.equal eff1.eff_ghostr eff2.eff_ghostr &&
  Sreg.equal eff1.eff_ghostw eff2.eff_ghostw &&
  Sexn.equal eff1.eff_ghostx eff2.eff_ghostx &&
  Mreg.equal (Opt.equal reg_equal) eff1.eff_resets eff2.eff_resets

let vtv_equal vtv1 vtv2 =
  vtv1.vtv_ghost = vtv2.vtv_ghost &&
  ity_equal vtv1.vtv_ity vtv2.vtv_ity &&
  Opt.equal reg_equal vtv1.vtv_mut vtv2.vtv_mut

let rec vta_compat a1 a2 =
  assert (List.for_all2 pv_equal a1.vta_args a2.vta_args);
  a1.vta_ghost = a2.vta_ghost &&
  (* no need to compare the rest of the spec, see below *)
  eff_equal a1.vta_spec.c_effect a2.vta_spec.c_effect &&
  match a1.vta_result, a2.vta_result with
  | VTarrow a1, VTarrow a2 -> vta_compat a1 a2
  | VTvalue v1, VTvalue v2 -> vtv_equal v1 v2
  | _,_ -> assert false

let ps_compat ps1 ps2 =
  vta_compat ps1.ps_vta ps2.ps_vta &&
  Mid.equal (fun _ _ -> true) ps1.ps_varm ps2.ps_varm

let rec expr_subst psm e = e_label_copy e (match e.e_node with
  | Earrow ps when Mid.mem ps.ps_name psm ->
      e_arrow (Mid.find ps.ps_name psm) (vta_of_expr e)
  | Eapp (e,pv,_) ->
      e_app_real (expr_subst psm e) pv
  | Elet ({ let_sym = LetV pv ; let_expr = d }, e) ->
      let nd = expr_subst psm d in
      let vtv = match nd.e_vty with VTvalue vtv -> vtv | _ -> assert false in
      if not (vtv_equal vtv pv.pv_vtv) then Loc.errorm "vty_value mismatch";
      e_let { let_sym = LetV pv ; let_expr = nd } (expr_subst psm e)
  | Elet ({ let_sym = LetA ps ; let_expr = d }, e) ->
      let ld = create_let_defn (id_clone ps.ps_name) (expr_subst psm d) in
      let ns = match ld.let_sym with LetA a -> a | LetV _ -> assert false in
      e_let ld (expr_subst (Mid.add ps.ps_name ns psm) e)
  | Erec (fdl, e) ->
      let conv lam = { lam with l_expr = expr_subst psm lam.l_expr } in
      let defl = List.map (fun fd -> fd.fun_ps, conv fd.fun_lambda) fdl in
      let fdl = create_rec_defn defl in
      let add psm (ps,_) fd = Mid.add ps.ps_name fd.fun_ps psm in
      e_rec fdl (expr_subst (List.fold_left2 add psm defl fdl) e)
  | Eif (e,e1,e2) ->
      e_if (expr_subst psm e) (expr_subst psm e1) (expr_subst psm e2)
  | Ecase (e,bl) ->
      let branch (pp,e) = pp, expr_subst psm e in
      e_case (expr_subst psm e) (List.map branch bl)
  | Eassign (e,_,pv) ->
      e_assign_real (expr_subst psm e) pv
  | Eghost e ->
      e_ghost (expr_subst psm e)
  | Eabstr (e,spec) ->
      e_abstract (expr_subst psm e) spec
  | Eraise (xs,e0) ->
      e_raise xs (expr_subst psm e0) (vtv_of_expr e).vtv_ity
  | Etry (e,bl) ->
      let branch (xs,pv,e) = xs, pv, expr_subst psm e in
      e_try (expr_subst psm e) (List.map branch bl)
  | Eloop (inv,var,e) ->
      e_loop inv var (expr_subst psm e)
  | Efor (pv,bounds,inv,e) ->
      e_for_real pv bounds inv (expr_subst psm e)
  | Elogic _ | Evalue _ | Earrow _ | Eany _ | Eabsurd | Eassert _ -> e)

and create_rec_defn defl =
  let add_sym acc (ps,_) = Sid.add ps.ps_name acc in
  let recsyms = List.fold_left add_sym Sid.empty defl in
  let conv m (ps,lam) =
    let fd = create_fun_defn (id_clone ps.ps_name) lam recsyms in
    if ps_compat ps fd.fun_ps then m, { fd with fun_ps = ps }
    else Mid.add ps.ps_name fd.fun_ps m, fd in
  let m, fdl = Lists.map_fold_left conv Mid.empty defl in
  if Mid.is_empty m then fdl else subst_fd m fdl

and subst_fd psm fdl =
  let subst { fun_ps = ps; fun_lambda = lam } =
    Mid.find_def ps ps.ps_name psm,
    { lam with l_expr = expr_subst psm lam.l_expr } in
  create_rec_defn (List.map subst fdl)

(* Before we start computing the fixpoint for effects, we must
   get the pre/post/xpost right. Therefore we require every ps
   participating in the recursion to have a first-order body,
   so that its spec (except the effect) is known from the start.
   Then we apply one round of substitution, to ensure that in
   each pair (ps,lam), the two sides have vty of the same shape
   and with the same final spec (except the effect). The result
   is passed to create_rec_defn above which repeats substitution
   until the effects are stabilized. TODO: prove correctness *)
let create_rec_defn = let letrec = ref 1 in fun defl ->
  if defl = [] then invalid_arg "Mlw_expr.create_rec_defn";
  (* check that the all variants use the same order *)
  let variant1 = (snd (List.hd defl)).l_spec.c_variant in
  let check_variant (_, { l_spec = { c_variant = vl }}) =
    let res = try List.for_all2 (fun (_,r1) (_,r2) ->
        Opt.equal ls_equal r1 r2) vl variant1
      with Invalid_argument _ -> false in
    if not res then Loc.errorm
      "All functions in a recursive definition \
        must use the same well-founded order for variant"
  in
  List.iter check_variant (List.tl defl);
  (* create the first list of fun_defns *)
  let add_sym acc (ps,_) = Sid.add ps.ps_name acc in
  let recsyms = List.fold_left add_sym Sid.empty defl in
  let conv m (ps,lam) = match lam.l_expr.e_vty with
    | VTarrow _ -> Loc.errorm ?loc:lam.l_expr.e_loc
        "The body of a recursive function must be a first-order value"
    | VTvalue _ ->
        if lam.l_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.create_rec_defn";
        let spec = { lam.l_spec with c_letrec = !letrec } in
        let lam = { lam with l_spec = spec } in
        let fd = create_fun_defn (id_clone ps.ps_name) lam recsyms in
        Mid.add ps.ps_name fd.fun_ps m, fd in
  let m, fdl = Lists.map_fold_left conv Mid.empty defl in
  incr letrec;
  subst_fd m fdl

let create_fun_defn id lam =
  if lam.l_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.create_fun_defn";
  create_fun_defn id lam Sid.empty

(* fold *)

let e_fold fn acc e = match e.e_node with
  | Elet (ld,e) -> fn (fn acc ld.let_expr) e
  | Erec (fdl,e) ->
      let fn_fd acc fd = fn acc fd.fun_lambda.l_expr in
      fn (List.fold_left fn_fd acc fdl) e
  | Ecase (e,bl) ->
      let fnbr acc (_,e) = fn acc e in
      List.fold_left fnbr (fn acc e) bl
  | Etry (e,bl) ->
      let fn_br acc (_,_,e) = fn acc e in
      List.fold_left fn_br (fn acc e) bl
  | Eif (e1,e2,e3) -> fn (fn (fn acc e1) e2) e3
  | Eapp (e,_,_) | Eassign (e,_,_) | Eghost e
  | Eloop (_,_,e) | Efor (_,_,_,e) | Eraise (_,e)
  | Eabstr (e,_) -> fn acc e
  | Elogic _ | Evalue _ | Earrow _
  | Eany _ | Eassert _ | Eabsurd -> acc

let spec_purify sp =
  let vs, f = Mlw_ty.open_post sp.c_post in
  match f.t_node with
  | Tapp (ps, [{t_node = Tvar us}; t])
    when ls_equal ps ps_equ && vs_equal vs us && not (Mvs.mem vs t.t_vars) ->
      t
  | Tbinop (Tiff, {t_node = Tapp (ps,[{t_node = Tvar us};{t_node = Ttrue}])},f)
    when ls_equal ps ps_equ && vs_equal vs us && not (Mvs.mem vs f.t_vars) ->
      t_if f t_bool_true t_bool_false
  | _ -> raise Exit

let rec e_purify e =
  let t = match e.e_node with
    | Elogic f when f.t_ty = None ->
        t_if f t_bool_true t_bool_false
    | Elogic t -> t
    | Evalue pv -> t_var pv.pv_vs
    | Earrow _ | Eassert _ -> t_void
    | Eapp (_,_,sp) -> spec_purify sp
    | Elet ({ let_sym = LetV pv; let_expr = e1 }, e2) ->
        t_let_close_simp pv.pv_vs (e_purify e1) (e_purify e2)
    | Elet ({ let_sym = LetA _ }, e1)
    | Erec (_,e1) | Eghost e1 ->
        e_purify e1
    | Eif (e1,e2,e3) ->
        t_if_simp (t_equ_simp (e_purify e1) t_bool_true)
          (e_purify e2) (e_purify e3)
    | Ecase (e1,bl) ->
        let conv (p,e) = t_close_branch p.ppat_pattern (e_purify e) in
        t_case (e_purify e1) (List.map conv bl)
    | Eany sp | Eabstr (_,sp) -> spec_purify sp
    | Eassign _ | Eloop _ | Efor _
    | Eraise _ | Etry _ | Eabsurd -> raise Exit
  in
  let loc = if t.t_loc = None then e.e_loc else t.t_loc in
  t_label ?loc (Slab.union e.e_label t.t_label) t

let e_purify e =
  if Sreg.is_empty e.e_effect.eff_writes &&
     Sreg.is_empty e.e_effect.eff_ghostw &&
     Sexn.is_empty e.e_effect.eff_raises &&
     Sexn.is_empty e.e_effect.eff_ghostx
  then try Some (e_purify e) with Exit -> None
  else None
