(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T

(** program/logic symbols *)

type field = {
  fd_ity   : ity;
  fd_ghost : bool;
  fd_mut   : region option;
}

type plsymbol = {
  pl_ls     : lsymbol;
  pl_args   : field list;
  pl_value  : field;
  pl_hidden : bool;
  pl_rdonly : bool;
}

let pl_equal : plsymbol -> plsymbol -> bool = (==)

let create_plsymbol_unsafe, restore_pl =
  let ls_to_pls = Wls.create 17 in
  (fun ls args value ~hidden ~rdonly ->
    let pl = {
      pl_ls     = ls;
      pl_args   = args;
      pl_value  = value;
      pl_hidden = hidden;
      pl_rdonly = rdonly;
    } in
    Wls.set ls_to_pls ls pl;
    pl),
  Wls.find ls_to_pls

let create_plsymbol ?(hidden=false) ?(rdonly=false) ?(constr=0) id args value =
  let ty_of_field fd =
    Opt.iter (fun r -> ity_equal_check fd.fd_ity r.reg_ity) fd.fd_mut;
    ty_of_ity fd.fd_ity in
  let pure_args = List.map ty_of_field args in
  let pure_value = ty_of_field value in
  (* plsymbols are used for constructors and projections, which are safe *)
  let opaque = List.fold_left ty_freevars Stv.empty (pure_value::pure_args) in
  let ls = create_fsymbol ~opaque ~constr id pure_args pure_value in
  create_plsymbol_unsafe ls args value ~hidden ~rdonly

let ity_of_ty_opt ty = ity_of_ty (Opt.get_def ty_bool ty)

let fake_field ty = { fd_ity = ity_of_ty ty; fd_ghost = false; fd_mut = None }

let fake_pls = Wls.memoize 17 (fun ls ->
  { pl_ls     = ls;
    pl_args   = List.map fake_field ls.ls_args;
    pl_value  = fake_field (Opt.get_def ty_bool ls.ls_value);
    pl_hidden = false;
    pl_rdonly = false; })

exception HiddenPLS of plsymbol
exception RdOnlyPLS of plsymbol

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
  let conv_field fd = {
    fd_ity   = conv_ity fd.fd_ity;
    fd_ghost = fd.fd_ghost;
    fd_mut   = Opt.map conv_reg fd.fd_mut }
  in
  let add_pl opls nls acc =
    let npls = try restore_pl nls with Not_found ->
      let args = List.map conv_field opls.pl_args in
      let value = conv_field opls.pl_value in
      let hidden = opls.pl_hidden in
      let rdonly = opls.pl_rdonly in
      create_plsymbol_unsafe nls args value ~hidden ~rdonly
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
  ppat_ity     : ity;
  ppat_ghost   : bool;  (* matches a ghost value *)
  ppat_fail    : bool;  (* refutable under ghost *)
}

type pre_ppattern =
  | PPwild
  | PPvar  of preid
  | PPlapp of lsymbol * pre_ppattern list
  | PPpapp of plsymbol * pre_ppattern list
  | PPor   of pre_ppattern * pre_ppattern
  | PPas   of pre_ppattern * preid

let make_ppattern pp ?(ghost=false) ity =
  let hv = Hstr.create 3 in
  let fail = ref false in
  let find id ghost ity =
    try
      let pv = Hstr.find hv id.pre_name in
      ity_equal_check ity pv.pv_ity;
      if (pv.pv_ghost <> ghost) then invalid_arg "Mlw_expr.make_ppattern";
      pv
    with Not_found ->
      let pv = create_pvsymbol id ~ghost ity in
      Hstr.add hv id.pre_name pv; pv
  in
  let rec make ghost ity = function
    | PPwild -> pat_wild (ty_of_ity ity)
    | PPvar id -> pat_var (find id ghost ity).pv_vs
    | PPpapp (pls,ppl) ->
        if pls.pl_hidden then raise (HiddenPLS pls);
        if pls.pl_ls.ls_constr = 0 then
          raise (Term.ConstructorExpected pls.pl_ls);
        if ghost && pls.pl_ls.ls_constr > 1 then fail := true;
        let ityv = pls.pl_value.fd_ity in
        let sbs = ity_match ity_subst_empty ityv ity in
        let mtch arg pp =
          let ghost = ghost || arg.fd_ghost in
          make ghost (ity_full_inst sbs arg.fd_ity) pp in
        let ppl = try List.map2 mtch pls.pl_args ppl with
          | Not_found -> raise (Term.ConstructorExpected pls.pl_ls)
          | Invalid_argument _ -> raise (Term.BadArity
              (pls.pl_ls, List.length ppl)) in
        pat_app pls.pl_ls ppl (ty_of_ity ity)
    | PPlapp (ls,ppl) ->
        if ls.ls_constr = 0 then
          raise (Term.ConstructorExpected ls);
        if ghost && ls.ls_constr > 1 then fail := true;
        let ityv = ity_of_ty_opt ls.ls_value in
        let sbs = ity_match ity_subst_empty ityv ity in
        let mtch arg pp =
          make ghost (ity_full_inst sbs (ity_of_ty arg)) pp in
        let ppl = try List.map2 mtch ls.ls_args ppl with
          | Not_found -> raise (Term.ConstructorExpected ls)
          | Invalid_argument _ -> raise (Term.BadArity
              (ls, List.length ppl)) in
        pat_app ls ppl (ty_of_ity ity)
    | PPor (pp1,pp2) ->
        pat_or (make ghost ity pp1) (make ghost ity pp2)
    | PPas (pp,id) ->
        pat_as (make ghost ity pp) (find id ghost ity).pv_vs;
  in
  let pat = make ghost ity pp in
  Hstr.fold Mstr.add hv Mstr.empty,
  { ppat_pattern = pat; ppat_ity = ity;
    ppat_ghost = ghost; ppat_fail = !fail }

(** program symbols *)

type psymbol = {
  ps_name  : ident;
  ps_aty   : aty;
  ps_ghost : bool;
  ps_pvset : Spv.t;
  ps_vars  : varset;
  ps_subst : ity_subst;
}

module Psym = MakeMSHW (struct
  type t = psymbol
  let tag ps = ps.ps_name.id_tag
end)

module Sps = Psym.S
module Mps = Psym.M
module Hps = Psym.H
module Wps = Psym.W

type symset = {
  syms_pv : Spv.t;
  syms_ps : Sps.t;
}

let ps_equal : psymbol -> psymbol -> bool = (==)

let add_pv_vars vars pv = vars_union vars pv.pv_ity.ity_vars
let add_ps_vars vars ps = vars_union vars ps.ps_vars

let create_psymbol_raw ~poly id ghost syms aty =
  let { syms_pv = pvset; syms_ps = psset } = syms in
  let tyvars = if poly then vars_empty else aty_vars aty in
  let pvvars = Spv.fold_left add_pv_vars vars_empty pvset in
  let psvars = Sps.fold_left add_ps_vars vars_empty psset in
  let vars = vars_union psvars (vars_union pvvars tyvars) in
  (* we must be polymorphic in every region not fixed by the context *)
  reg_iter (fun reg -> if not (reg_occurs reg pvvars) then Loc.errorm
    "This partial application produces non-generalizable effects") tyvars;
  assert (reg_all (fun reg -> reg_occurs reg pvvars) psvars);
  { ps_name  = id_register id;
    ps_aty   = aty_filter ~ghost pvset aty;
    ps_ghost = ghost;
    ps_pvset = pvset;
    ps_vars  = vars;
    ps_subst = vars_freeze vars; }

(** specification *)

let rec aty_check vars aty =
  if aty.aty_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.aty_check";
  let test_or_raise c = if not c then Loc.errorm
    "every external effect must be mentioned in specification" in
  let vars = List.fold_left add_pv_vars vars aty.aty_args in
  let ch_tv tv = test_or_raise (Stv.mem tv vars.vars_tv) in
  let check reg = test_or_raise (reg_occurs reg vars) in
  let eff = aty.aty_spec.c_effect in
  Sreg.iter check eff.eff_writes;
  Sreg.iter check eff.eff_ghostw;
  Stv.iter  ch_tv eff.eff_compar;
  match aty.aty_result with
  | VTarrow a -> aty_check vars a
  | VTvalue _ -> ()

let create_psymbol id ?(ghost=false) aty =
  let syms = { syms_pv = aty_pvset aty; syms_ps = Sps.empty } in
  let vars = Spv.fold_left add_pv_vars vars_empty syms.syms_pv in
  aty_check vars aty;
  create_psymbol_raw ~poly:true id ghost syms aty

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
  e_ghost  : bool;
  e_effect : effect;
  e_syms   : symset;
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
  | Eassign of plsymbol * expr * region * pvsymbol
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
  fun_syms   : symset;
}

and lambda = {
  l_args : pvsymbol list;
  l_expr : expr;
  l_spec : spec;
}

(* symset manipulation *)

let syms_empty = {
  syms_pv = Spv.empty;
  syms_ps = Sps.empty;
}

let del_pv_syms pv syms = {
(* TODO/FIXME: removing a pvsymbol directly from syms_pv may break
   the symset invariant requiring that all pvs in syms_ps*ps_pvset
   were in syms_pv. This is only possible if one reuses a let_defn
   in an expr, and reusing let_defn breaks WP anyway, so we ignore
   this for now, until a proper variable binding is implemented. *)
  syms_pv = Spv.remove pv syms.syms_pv;
  syms_ps = syms.syms_ps;
}

let del_ps_syms ps syms = {
  syms_pv = syms.syms_pv;
  syms_ps = Sps.remove ps syms.syms_ps;
}

let add_pv_syms pv syms = {
  syms_pv = Spv.add pv syms.syms_pv;
  syms_ps = syms.syms_ps;
}

let add_ps_syms ps syms = {
  syms_pv = Spv.union ps.ps_pvset syms.syms_pv;
  syms_ps = Sps.add ps syms.syms_ps;
}

let add_e_syms e syms = {
  syms_pv = Spv.union e.e_syms.syms_pv syms.syms_pv;
  syms_ps = Sps.union e.e_syms.syms_ps syms.syms_ps;
}

let add_t_syms t syms = {
  syms_pv = t_pvset syms.syms_pv t;
  syms_ps = syms.syms_ps;
}

let add_spec_syms c syms = {
  syms_pv = spec_pvset syms.syms_pv c;
  syms_ps = syms.syms_ps;
}

let syms_union syms1 syms2 = {
  syms_pv = Spv.union syms1.syms_pv syms2.syms_pv;
  syms_ps = Sps.union syms1.syms_ps syms2.syms_ps;
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

let ity_of_expr e = match e.e_vty with
  | VTvalue ity -> ity
  | VTarrow _ -> Loc.error ?loc:e.e_loc (ValueExpected e)

let aty_of_expr e = match e.e_vty with
  | VTvalue _ -> Loc.error ?loc:e.e_loc (ArrowExpected e)
  | VTarrow aty -> aty

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
  | Eapp (e,_,_) | Eassign (_,e,_,_) | Eghost e
  | Eloop (_,_,e) | Efor (_,_,_,e) | Eraise (_,e)
  | Eabstr (e,_) -> fn acc e
  | Elogic _ | Evalue _ | Earrow _
  | Eany _ | Eassert _ | Eabsurd -> acc

exception Found of expr

let e_find pr e =
  let rec find () e =
    e_fold find () e;
    if pr e then raise (Found e) in
  try find () e; raise Not_found with Found e -> e

(* check admissibility of consecutive events *)

exception StaleRegion of expr * ident

let check_reset e { syms_pv = spv; syms_ps = sps } =
  (* If we reset a region, then it may only occur in the later code
     as the result of the resetting expression. Otherwise, this is
     a freshness violation: some symbol defined earlier carries that
     region into the later code. *)
  let check id vars = if eff_stale_region e.e_effect vars then
    Loc.error ?loc:e.e_loc (StaleRegion (e,id)) in
  if not (Mreg.is_empty e.e_effect.eff_resets) then begin
    Sps.iter (fun ps -> check ps.ps_name ps.ps_vars) sps;
    Spv.iter (fun pv -> check pv.pv_vs.vs_name pv.pv_ity.ity_vars) spv
  end

let check_ghost_write { eff_ghostw = regs } { syms_pv = pvs } =
  let check { pv_ghost = gh; pv_ity = ity } =
    if not gh && lookup_nonghost_reg regs ity then Loc.errorm
      "This expression makes a ghost write into a non-ghost location" in
  if not (Sreg.is_empty regs) then Spv.iter check pvs

let check_postexpr e _eff syms =
  check_reset e syms

(* smart constructors *)

let mk_expr node vty ghost eff syms =
  let ghost = ghost || not (Sexn.is_empty eff.eff_ghostx) in
  let eff = eff_ghostify ghost eff in
  check_ghost_write eff syms;
  { e_node   = node;
    e_vty    = vty;
    e_ghost  = ghost;
    e_effect = eff;
    e_syms   = syms;
    e_label  = Slab.empty;
    e_loc    = None; }

(* program variables and program symbols *)

let e_value pv =
  let syms = add_pv_syms pv syms_empty in
  mk_expr (Evalue pv) (VTvalue pv.pv_ity) pv.pv_ghost eff_empty syms

let e_arrow ps argl res =
  let syms = add_ps_syms ps syms_empty in
  let sbs = aty_vars_match ps.ps_subst ps.ps_aty argl res in
  let aty = aty_full_inst sbs ps.ps_aty in
  mk_expr (Earrow ps) (VTarrow aty) ps.ps_ghost eff_empty syms

let e_arrow_aty ps aty =
  let rec get_types argl a =
    let add argl pv = pv.pv_ity :: argl in
    let argl = List.fold_left add argl a.aty_args in
    match a.aty_result with
    | VTarrow a -> get_types argl a
    | VTvalue v -> e_arrow ps (List.rev argl) v
  in
  get_types [] aty

(* let-definitions *)

let create_let_defn id e =
  let lv = match e.e_vty with
    | VTarrow aty ->
        let rec is_value e = match e.e_node with
          | Earrow _ -> true
          | Erec ([fd], {e_node = Earrow ps}) -> (* (fun ... -> ...) *)
              ps_equal fd.fun_ps ps && fd.fun_lambda.l_spec.c_letrec = 0
          | Eany spec -> eff_is_empty spec.c_effect (* && empty spec? *)
          | Eghost e -> is_value e
          | _ -> false in
        LetA (create_psymbol_raw ~poly:(is_value e) id e.e_ghost e.e_syms aty)
    | VTvalue ity ->
        LetV (create_pvsymbol id ~ghost:e.e_ghost ity) in
  { let_sym = lv ; let_expr = e }

let create_let_pv_defn id e =
  let ld = create_let_defn id e in
  match ld.let_sym with
    | LetA _ -> Loc.error ?loc:e.e_loc (ValueExpected e)
    | LetV pv -> ld, pv

let create_let_ps_defn id e =
  let ld = create_let_defn id e in
  match ld.let_sym with
    | LetV _ -> Loc.error ?loc:e.e_loc (ArrowExpected e)
    | LetA ps -> ld, ps

let e_let ({ let_sym = lv ; let_expr = d } as ld) e =
  let syms = match lv with
    | LetV pv -> del_pv_syms pv e.e_syms
    | LetA ps -> del_ps_syms ps e.e_syms in
  check_postexpr d e.e_effect syms;
  let eff = eff_union d.e_effect e.e_effect in
  mk_expr (Elet (ld,e)) e.e_vty e.e_ghost eff (add_e_syms d syms)

let on_value fn e = match e.e_node with
  | Evalue pv -> fn pv
  | _ ->
      let ld,pv = create_let_pv_defn (id_fresh ?loc:e.e_loc "o") e in
      e_let ld (fn pv)

(* application *)

let e_app_real e pv =
  let spec,ghost,vty = aty_app (aty_of_expr e) pv in
  let ghost = e.e_ghost || ghost in
  let eff = eff_ghostify ghost spec.c_effect in
  check_postexpr e eff (add_pv_syms pv syms_empty);
  let eff = eff_union e.e_effect eff in
  mk_expr (Eapp (e,pv,spec)) vty ghost eff (add_pv_syms pv e.e_syms)

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

let e_app e1 e2 = on_value (fun pv -> e_app_flatten e1 pv) e2
let e_app e1 el = List.fold_left e_app e1 el

let e_plapp pls el ity =
  if pls.pl_hidden then raise (HiddenPLS pls);
  if pls.pl_rdonly then raise (RdOnlyPLS pls);
  let rec app tl syms ghost eff sbs fdl argl = match fdl, argl with
    | [],[] ->
        let mut_fold leff fd = Opt.fold eff_reset leff fd.fd_mut in
        let leff = List.fold_left mut_fold eff_empty pls.pl_args in
        let mtv = Mtv.set_diff sbs.ity_subst_tv pls.pl_ls.ls_opaque in
        let leff = Mtv.fold (fun tv _ e -> eff_compare e tv) mtv leff in
        let eff = eff_union eff (eff_full_inst sbs leff) in
        let t = match pls.pl_ls.ls_value with
          | Some _ -> fs_app pls.pl_ls tl (ty_of_ity ity)
          | None   -> ps_app pls.pl_ls tl in
        mk_expr (Elogic t) (VTvalue ity) ghost eff syms
    | [],_ | _,[] ->
        raise (Term.BadArity (pls.pl_ls, List.length el))
    | fd::fdl, ({ e_node = Elogic t } as e)::argl
      when Spv.for_all (fun pv -> ity_immutable pv.pv_ity) e.e_syms.syms_pv ->
        let t = match t.t_ty with
          | Some _ -> t
          | None -> t_if_simp t t_bool_true t_bool_false in
        let ghost = ghost || (e.e_ghost && not fd.fd_ghost) in
        if fd.fd_ghost && not e.e_ghost then
          Loc.errorm "non-ghost value passed as a ghost argument";
        let eff = eff_union eff e.e_effect in
        let sbs = ity_match sbs fd.fd_ity (ity_of_expr e) in
        app (t::tl) (add_e_syms e syms) ghost eff sbs fdl argl
    | fd::fdl, e::argl ->
        let apply_to_pv pv =
          let t = t_var pv.pv_vs in
          let ghost = ghost || (pv.pv_ghost && not fd.fd_ghost) in
          let sbs = ity_match sbs fd.fd_ity pv.pv_ity in
          app (t::tl) (add_pv_syms pv syms) ghost eff sbs fdl argl
        in
        if fd.fd_ghost && not e.e_ghost then
          Loc.errorm "non-ghost value passed as a ghost argument";
        on_value apply_to_pv e
  in
  let argl = List.rev el and fdl = List.rev pls.pl_args in
  let sbs = ity_match ity_subst_empty pls.pl_value.fd_ity ity in
  app [] syms_empty pls.pl_value.fd_ghost eff_empty sbs fdl argl

let e_lapp ls el ity = e_plapp (fake_pls ls) el ity

let fs_void = fs_tuple 0
let t_void = fs_app fs_void [] ty_unit
let e_void = e_lapp fs_void [] ity_unit

(* if and match *)

let e_if e0 e1 e2 =
  ity_equal_check (ity_of_expr e0) ity_bool;
  ity_equal_check (ity_of_expr e1) (ity_of_expr e2);
  let eff = eff_union e1.e_effect e2.e_effect in
  let syms = add_e_syms e2 (add_e_syms e1 syms_empty) in
  let ghost = e0.e_ghost || e1.e_ghost || e2.e_ghost in
  let eff = eff_ghostify ghost eff in
  check_postexpr e0 eff syms;
  let syms = add_e_syms e0 syms in
  let eff = eff_union e0.e_effect eff in
  mk_expr (Eif (e0,e1,e2)) e1.e_vty ghost eff syms

let e_case e0 bl =
  let bity = match bl with
    | (_,e)::_ -> ity_of_expr e
    | [] -> raise Term.EmptyCase in
  let rec branch ghost eff syms = function
    | (pp,e)::bl ->
        if e0.e_ghost <> pp.ppat_ghost then
          Loc.errorm "Invalid pattern ghost status";
        ity_equal_check (ity_of_expr e0) pp.ppat_ity;
        ity_equal_check (ity_of_expr e) bity;
        let eff = eff_union eff e.e_effect in
        let del_vs vs _ syms = del_pv_syms (restore_pv vs) syms in
        let bsyms = Mvs.fold del_vs pp.ppat_pattern.pat_vars e.e_syms in
        let ghost = ghost || pp.ppat_fail || e.e_ghost in
        branch ghost eff (syms_union syms bsyms) bl
    | [] ->
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = eff_ghostify ghost eff in
        check_postexpr e0 eff syms; (* cumulated symset *)
        let eff = eff_union e0.e_effect eff in
        let syms = add_e_syms e0 syms in
        mk_expr (Ecase (e0,bl)) (VTvalue bity) ghost eff syms
  in
  (* one-branch match is not ghost even if the matched value is *)
  branch (e0.e_ghost && List.length bl > 1) eff_empty syms_empty bl

(* ghost *)

let e_ghost e =
  mk_expr (Eghost e) e.e_vty true e.e_effect e.e_syms

(* assignment *)

exception Immutable of expr

let e_assign_real pls e0 pv =
  if pls.pl_hidden then raise (HiddenPLS pls);
  if pls.pl_rdonly then raise (RdOnlyPLS pls);
  let r = match pls.pl_value.fd_mut, pls.pl_args with
    (* if pls.pl_value is mutable, it can only be a projection *)
    | Some r, [{fd_ity = {ity_node = Ityapp (s,_,_)} as ity}] ->
        if s.its_priv then raise (RdOnlyPLS pls);
        let sbs = ity_match ity_subst_empty ity (ity_of_expr e0) in
        reg_full_inst sbs r
    | _,_ ->
        raise (Immutable (e_plapp pls [e0] pv.pv_ity)) in
  let lghost = e0.e_ghost || pls.pl_value.fd_ghost in
  let ghost = lghost || pv.pv_ghost in
  let eff = eff_assign eff_empty ~ghost r pv.pv_ity in
  let syms = add_pv_syms pv syms_empty in
  check_postexpr e0 eff syms;
  let syms = add_e_syms e0 syms in
  let eff = eff_union eff e0.e_effect in
  mk_expr (Eassign (pls,e0,r,pv)) (VTvalue ity_unit) ghost eff syms

let e_assign pls e0 e1 = on_value (e_assign_real pls e0) e1

(* numeric constants *)

let e_from_t t =
  mk_expr (Elogic t) (VTvalue (ity_of_ty_opt t.t_ty)) false eff_empty syms_empty

let e_const c ity = e_from_t (t_const c (ty_of_ity ity))

(* boolean expressions *)

(* FIXME? Should we rather use boolean constants here? *)
let e_true =
  mk_expr (Elogic t_true) (VTvalue ity_bool) false eff_empty syms_empty

let e_false =
  mk_expr (Elogic t_false) (VTvalue ity_bool) false eff_empty syms_empty

let on_fmla fn e = match e.e_node with
  | Elogic ({ t_ty = None } as f) -> fn e f
  | Elogic t -> fn e (t_equ_simp t t_bool_true)
  | Evalue pv -> fn e (t_equ_simp (t_var pv.pv_vs) t_bool_true)
  | _ ->
      let ld,pv = create_let_pv_defn (id_fresh ?loc:e.e_loc "o") e in
      e_let ld (fn (e_value pv) (t_equ_simp (t_var pv.pv_vs) t_bool_true))

let e_not e =
  on_fmla (fun e f ->
    ity_equal_check (ity_of_expr e) ity_bool;
    mk_expr (Elogic (t_not f)) e.e_vty e.e_ghost e.e_effect e.e_syms) e

let e_binop op e1 e2 =
  on_fmla (fun e1 f1 -> on_fmla (fun e2 f2 ->
    ity_equal_check (ity_of_expr e1) ity_bool;
    ity_equal_check (ity_of_expr e2) ity_bool;
    let syms = add_e_syms e1 e2.e_syms in
    let eff = eff_union e1.e_effect e2.e_effect in
    let ghost = e1.e_ghost || e2.e_ghost in
    mk_expr (Elogic (t_binary op f1 f2)) e1.e_vty ghost eff syms) e2) e1

let rec e_nospec e = match e.e_node with
  | Elogic _ | Evalue _ -> true
  | Eif (e1,e2,e3) -> e_nospec e1 && e_nospec e2 && e_nospec e3
  | Ecase (e1,bl) -> e_nospec e1 && List.for_all (fun (_,e2) -> e_nospec e2) bl
  | Elet ({let_sym = LetV _; let_expr = e1}, e2) -> e_nospec e1 && e_nospec e2
  | Eghost e1 -> e_nospec e1
  | _ -> false

let e_lazy_and e1 e2 =
  if eff_is_empty e2.e_effect && e_nospec e2
  then e_binop Tand e1 e2 else e_if e1 e2 e_false

let e_lazy_or e1 e2 =
  if eff_is_empty e2.e_effect && e_nospec e2
  then e_binop Tor e1 e2 else e_if e1 e_true e2

(* loops *)

let e_loop inv variant ({e_effect = eff} as e) =
  ity_equal_check (ity_of_expr e) ity_unit;
  let syms = List.fold_left (fun s (t,_) ->
    add_t_syms t s) e.e_syms variant in
  let syms = add_t_syms inv syms in
  check_postexpr e eff syms;
  let eff = if variant = [] then eff_diverge eff else eff in
  mk_expr (Eloop (inv,variant,e)) e.e_vty e.e_ghost eff syms

let e_for_real pv bounds inv e =
  let pvfrom,_,pvto = bounds in
  ity_equal_check (ity_of_expr e) ity_unit;
  ity_equal_check pv.pv_ity ity_int;
  ity_equal_check pvfrom.pv_ity ity_int;
  ity_equal_check pvto.pv_ity ity_int;
  let ghost = pv.pv_ghost || pvfrom.pv_ghost || pvto.pv_ghost || e.e_ghost in
  let eff = eff_ghostify ghost e.e_effect in
  let syms = add_t_syms inv e.e_syms in
  (* FIXME? We check that no variable in the loop body, _including_
     the index variable, is not invalidated because of a region reset.
     We ignore the loop bounds, since they are computed just once. *)
  check_postexpr e eff syms;
  let syms = del_pv_syms pv syms in
  let syms = add_pv_syms pvfrom (add_pv_syms pvto syms) in
  mk_expr (Efor (pv,bounds,inv,e)) e.e_vty ghost eff syms

let e_for pv efrom dir eto inv e =
  let apply pvto pvfrom = e_for_real pv (pvfrom,dir,pvto) inv e in
  let apply pvto = on_value (apply pvto) efrom in
  on_value apply eto

(* raise and try *)

let e_raise xs e ity =
  ity_equal_check (ity_of_expr e) xs.xs_ity;
  let eff = eff_raise eff_empty ~ghost:e.e_ghost xs in
  check_postexpr e eff syms_empty;
  let eff = eff_union eff e.e_effect in
  mk_expr (Eraise (xs,e)) (VTvalue ity) e.e_ghost eff e.e_syms

let e_try e0 bl =
  let rec branch ghost eff syms = function
    | (xs,pv,e)::bl ->
        ity_equal_check (ity_of_expr e) (ity_of_expr e0);
        ity_equal_check pv.pv_ity xs.xs_ity;
        (* we don't care about pv being ghost *)
        let ghost = ghost || e.e_ghost in
        let eff = eff_union eff e.e_effect in
        let bsyms = del_pv_syms pv e.e_syms in
        branch ghost eff (syms_union syms bsyms) bl
    | [] ->
        (* the cumulated effect of all branches, w/out e0 *)
        let eff = eff_ghostify ghost eff in
        check_postexpr e0 eff syms; (* cumulated symset *)
        (* remove from e0.e_effect the catched exceptions *)
        let remove eff0 (xs,_,_) = eff_remove_raise eff0 xs in
        let eff0 = List.fold_left remove e0.e_effect bl in
        (* total effect and symset *)
        let eff = eff_union eff0 eff in
        let syms = add_e_syms e0 syms in
        mk_expr (Etry (e0,bl)) e0.e_vty ghost eff syms
  in
  branch e0.e_ghost eff_empty syms_empty bl

(* specification-related expressions *)

let pv_dummy = create_pvsymbol (id_fresh "dummy") ity_unit

let e_any spec vty =
  let aty = vty_arrow [pv_dummy] ?spec vty in
  let ps = create_psymbol (id_fresh "dummy") aty in
  let syms = del_ps_syms ps (add_ps_syms ps syms_empty) in
  let vty = ps.ps_aty.aty_result in
  let spec = ps.ps_aty.aty_spec in
  mk_expr (Eany spec) vty false spec.c_effect syms

let e_abstract ({ e_effect = eff } as e) spec =
  if spec.c_letrec <> 0 then invalid_arg "Mlw_expr.e_abstract";
  let spec = { spec with c_effect = eff } in
  spec_check ~full_xpost:false spec e.e_vty;
  let syms = add_spec_syms spec e.e_syms in
  mk_expr (Eabstr (e,spec)) e.e_vty e.e_ghost e.e_effect syms

let e_assert ak f =
  let syms = add_t_syms f syms_empty in
  mk_expr (Eassert (ak, f)) (VTvalue ity_unit) false eff_empty syms

let e_absurd ity =
  mk_expr Eabsurd (VTvalue ity) false eff_empty syms_empty

(* simple functional definitions *)

let create_fun_defn id ({l_expr = e; l_spec = c} as lam) =
  let eff = if c.c_letrec <> 0 && c.c_variant = []
    then eff_diverge e.e_effect else e.e_effect in
  let spec = { c with c_effect = eff } in
  let lam = { lam with l_spec = spec } in
  let syms = add_spec_syms lam.l_spec lam.l_expr.e_syms in
  let syms = List.fold_right del_pv_syms lam.l_args syms in
  let aty = vty_arrow lam.l_args ~spec e.e_vty in
  { fun_ps     = create_psymbol_raw ~poly:true id e.e_ghost syms aty;
    fun_lambda = lam;
    fun_syms   = syms; }

let e_rec fdl e =
  (* check letrec *)
  let fd, rest = match fdl with
    | [] -> invalid_arg "Mlw_expr.e_rec"
    | fd :: fdl -> fd, fdl in
  let lr = fd.fun_ps.ps_aty.aty_spec.c_letrec in
  let bad fd = fd.fun_ps.ps_aty.aty_spec.c_letrec <> lr in
  if List.exists bad rest then invalid_arg "Mlw_expr.e_rec";
  if lr = 0 && rest <> [] then invalid_arg "Mlw_expr.e_rec";
  (* compute syms *)
  let add_fd syms fd = syms_union fd.fun_syms syms in
  let del_fd syms fd = del_ps_syms fd.fun_ps syms in
  let syms = List.fold_left add_fd e.e_syms fdl in
  let syms = List.fold_left del_fd syms fdl in
  mk_expr (Erec (fdl,e)) e.e_vty e.e_ghost e.e_effect syms

(* compute the fixpoint on recursive definitions *)

let rec aty_compat a1 a2 =
  assert (List.for_all2 pv_equal a1.aty_args a2.aty_args);
  (* no need to compare the rest of the spec, see below *)
  eff_equal a1.aty_spec.c_effect a2.aty_spec.c_effect &&
  match a1.aty_result, a2.aty_result with
  | VTarrow a1, VTarrow a2 -> aty_compat a1 a2
  | VTvalue v1, VTvalue v2 -> ity_equal v1 v2
  | _,_ -> assert false

let ps_compat ps1 ps2 =
  aty_compat ps1.ps_aty ps2.ps_aty &&
  ps1.ps_ghost = ps2.ps_ghost &&
  Spv.equal ps1.ps_pvset ps2.ps_pvset &&
  Stv.equal ps1.ps_vars.vars_tv ps2.ps_vars.vars_tv &&
  Sreg.equal ps1.ps_vars.vars_reg ps2.ps_vars.vars_reg

let rec expr_subst psm e = e_label_copy e (match e.e_node with
  | Earrow ps when Mps.mem ps psm ->
      e_arrow_aty (Mps.find ps psm) (aty_of_expr e)
  | Eapp (e,pv,_) ->
      e_app_real (expr_subst psm e) pv
  | Elet ({ let_sym = LetV pv; let_expr = d }, e) ->
      let nd = expr_subst psm d in
      if not (ity_equal (ity_of_expr nd) pv.pv_ity) then
        Loc.errorm "vty_value mismatch";
      e_let { let_sym = LetV pv; let_expr = nd } (expr_subst psm e)
  | Elet ({ let_sym = LetA ps; let_expr = d }, e) ->
      let ld,ns = create_let_ps_defn (id_clone ps.ps_name) (expr_subst psm d) in
      e_let ld (expr_subst (Mps.add ps ns psm) e)
  | Erec ([{fun_ps = ps; fun_lambda = lam}], e) when lam.l_spec.c_letrec = 0 ->
      let lam = { lam with l_expr = expr_subst psm lam.l_expr } in
      let fd = create_fun_defn (id_clone ps.ps_name) lam in
      e_rec [fd] (expr_subst (Mps.add ps fd.fun_ps psm) e)
  | Erec (fdl, e) ->
      let conv lam = { lam with l_expr = expr_subst psm lam.l_expr } in
      let defl = List.map (fun fd -> fd.fun_ps, conv fd.fun_lambda) fdl in
      let fdl = create_rec_defn defl in
      let add psm (ps,_) fd = Mps.add ps fd.fun_ps psm in
      e_rec fdl (expr_subst (List.fold_left2 add psm defl fdl) e)
  | Eif (e,e1,e2) ->
      e_if (expr_subst psm e) (expr_subst psm e1) (expr_subst psm e2)
  | Ecase (e,bl) ->
      let branch (pp,e) = pp, expr_subst psm e in
      e_case (expr_subst psm e) (List.map branch bl)
  | Eassign (pls,e,_,pv) ->
      e_assign_real pls (expr_subst psm e) pv
  | Eghost e ->
      e_ghost (expr_subst psm e)
  | Eabstr (e,spec) ->
      e_abstract (expr_subst psm e) spec
  | Eraise (xs,e0) ->
      e_raise xs (expr_subst psm e0) (ity_of_expr e)
  | Etry (e,bl) ->
      let branch (xs,pv,e) = xs, pv, expr_subst psm e in
      e_try (expr_subst psm e) (List.map branch bl)
  | Eloop (inv,var,e) ->
      e_loop inv var (expr_subst psm e)
  | Efor (pv,bounds,inv,e) ->
      e_for_real pv bounds inv (expr_subst psm e)
  | Elogic _ | Evalue _ | Earrow _ | Eany _ | Eabsurd | Eassert _ -> e)

and create_rec_defn defl =
  let conv m (ps,lam) =
    let fd = create_fun_defn (id_clone ps.ps_name) lam in
    if ps_compat ps fd.fun_ps then m, { fd with fun_ps = ps }
    else Mps.add ps fd.fun_ps m, fd in
  let m, fdl = Lists.map_fold_left conv Mps.empty defl in
  if Mps.is_empty m then fdl else subst_fd m fdl

and subst_fd psm fdl =
  let subst { fun_ps = ps; fun_lambda = lam } =
    Mps.find_def ps ps psm,
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
  (* Check that all variants use compatible orders for their
     first component. *)
  let variant1 = (snd (List.hd defl)).l_spec.c_variant in
  let check_variant (_, { l_spec = { c_variant = vl }}) =
    match variant1, vl with
    | [], []
    | (_,None)::_, (_,None)::_ -> ()
    | (t1, Some r1)::_, (t2, Some r2)::_
      when oty_equal t1.t_ty t2.t_ty && ls_equal r1 r2 -> ()
    | _ -> Loc.errorm "All functions in a recursive definition \
        must use the same well-founded order for the first variant component"
  in
  List.iter check_variant (List.tl defl);
  (* create the first list of fun_defns *)
  let conv m (ps,lam) = match lam.l_expr.e_vty with
    | VTarrow _ -> Loc.errorm ?loc:lam.l_expr.e_loc
        "The body of a recursive function must be a first-order value"
    | VTvalue _ ->
        if lam.l_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.create_rec_defn";
        let spec = { lam.l_spec with c_letrec = !letrec } in
        let lam = { lam with l_spec = spec } in
        let fd = create_fun_defn (id_clone ps.ps_name) lam in
        Mps.add ps fd.fun_ps m, fd in
  let m, fdl = Lists.map_fold_left conv Mps.empty defl in
  incr letrec;
  subst_fd m fdl

let create_fun_defn id lam =
  if lam.l_spec.c_letrec <> 0 then invalid_arg "Mlw_expr.create_fun_defn";
  create_fun_defn id lam

(* expr to term *)

let spec_purify sp =
  let vs, f = Mlw_ty.open_post sp.c_post in
  match f.t_node with
  | Tapp (ps, [{t_node = Tvar us}; t])
    when ls_equal ps ps_equ && vs_equal vs us && t_v_occurs vs t = 0 ->
      t
  | Tbinop (Tiff, {t_node = Tapp (ps,[{t_node = Tvar us};{t_node = Ttrue}])},f)
    when ls_equal ps ps_equ && vs_equal vs us && t_v_occurs vs f = 0 ->
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
