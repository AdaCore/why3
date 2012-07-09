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
open Decl
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

let debug = Debug.register_flag "whyml_wp"

(** Marks *)

let ts_mark = create_tysymbol (id_fresh "'mark") [] None
let ty_mark = ty_app ts_mark []

let vtv_mark = vty_value (ity_pur ts_mark [])

let fresh_mark () = create_vsymbol (id_fresh "'mark") ty_mark

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let th_mark_at =
  let uc = create_theory (id_fresh "WP builtins: at") in
  let uc = add_ty_decl uc ts_mark in
  let uc = add_param_decl uc fs_at in
  close_theory uc

let th_mark_old =
  let uc = create_theory (id_fresh "WP builtins: old") in
  let uc = use_export uc th_mark_at in
  let uc = add_param_decl uc fs_old in
  close_theory uc

let fs_now = create_lsymbol (id_fresh "'now") [] (Some ty_mark)
let t_now = fs_app fs_now [] ty_mark
let e_now = e_lapp fs_now [] (ity_pur ts_mark [])

(* [vs_old] appears in the postconditions given to the core API,
   which expects every vsymbol to be a pure part of a pvsymbol *)
let pv_old = create_pvsymbol (id_fresh "'old") vtv_mark
let vs_old = pv_old.pv_vs
let t_old  = t_var vs_old

let t_at_old t = t_app fs_at [t; t_old] t.t_ty

let ls_absurd = create_lsymbol (id_fresh "absurd") [] None
let t_absurd  = ps_app ls_absurd []

let mk_t_if f = t_if f t_bool_true t_bool_false
let to_term t = if t.t_ty = None then mk_t_if t else t

(* any vs in post/xpost is either a pvsymbol or a fresh mark *)
let vtv_of_vs vs =
  try (restore_pv vs).pv_vtv with UnboundVar _ -> vtv_mark

(* replace every occurrence of [old(t)] with [at(t,'old)] *)
let rec remove_old f = match f.t_node with
  | Tapp (ls,[t]) when ls_equal ls fs_old -> t_at_old (remove_old t)
  | _ -> t_map remove_old f

(* FIXME? Do we need this? *)
(* replace every occurrence of [at(t,'now)] with [t] *)
let rec remove_at f = match f.t_node with
  | Tapp (ls, [t; { t_node = Tapp (fs,[]) }])
    when ls_equal ls fs_at && ls_equal fs fs_now -> remove_at t
  | _ -> t_map remove_at f

(* replace [at(t,'old)] with [at(t,lab)] everywhere in formula [f] *)
let old_mark lab t = t_subst_single vs_old (t_var lab) t

(* replace [at(t,lab)] with [at(t,'now)] everywhere in formula [f] *)
let erase_mark lab t = t_subst_single lab t_now t

(* TODO: explain this *)
let relativize fn q xq =
  let lab = fresh_mark () in
  let f = fn (old_mark lab q) (Mexn.map (old_mark lab) xq) in
  erase_mark lab f

(* replace [at(t,now)] with [t] modulo variable renaming *)
let rec drop_at now m t = match t.t_node with
  | Tvar vs when now ->
      begin try t_var (Mvs.find vs m) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls fs_old ->
      assert false
  | Tapp (ls, [e; mark]) when ls_equal ls fs_at ->
      begin match mark.t_node with
        | Tvar vs when vs_equal vs vs_old -> assert false
        | Tapp (ls,[]) when ls_equal ls fs_now -> drop_at true m e
        (* no longer assume that unmarked variables are at 'now *)
        | _ -> t_map (drop_at false m) t
      end
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      (* do not open unless necessary *)
      let m = Mvs.set_inter m t.t_vars in
      if Mvs.is_empty m then t else
      t_map (drop_at now m) t
  | _ ->
      t_map (drop_at now m) t

(** Specifications *)

let psymbol_spec_t : type_v Wps.t = Wps.create 17
let e_apply_spec_t : type_c Wexpr.t = Wexpr.create 17

let add_pv_varm pv m = Mid.add pv.pv_vs.vs_name pv.pv_vtv.vtv_vars m
let add_pv_vars pv s = vars_union pv.pv_vtv.vtv_vars s

let rec check_spec vty tyv = match vty, tyv with
  | VTvalue _, SpecV _ -> ()
  | VTarrow vta, SpecA (_::(_::_ as pvl), tyc) ->
      assert (eff_is_empty vta.vta_effect);
      check_spec vta.vta_result (SpecA (pvl, tyc))
  | VTarrow vta, SpecA ([_], tyc) ->
      let eff1 = vta.vta_effect in
      let eff2 = tyc.c_effect in
      assert (Sreg.equal eff1.eff_reads  eff2.eff_reads);
      assert (Sreg.equal eff1.eff_writes eff2.eff_writes);
      assert (Sexn.equal eff1.eff_raises eff2.eff_raises);
      assert (Sreg.equal eff1.eff_ghostr eff2.eff_ghostr);
      assert (Sreg.equal eff1.eff_ghostw eff2.eff_ghostw);
      assert (Sexn.equal eff1.eff_ghostx eff2.eff_ghostx);
      check_spec vta.vta_result tyc.c_result
  | _ -> assert false

let rec filter_v varm vars = function
  | SpecA (pvl, tyc) ->
      let varm = List.fold_right add_pv_varm pvl varm in
      let vars = List.fold_right add_pv_vars pvl vars in
      SpecA (pvl, filter_c varm vars tyc)
  | tyv -> tyv

and filter_c varm vars tyc =
  let add _ f s = Mvs.set_union f.t_vars s in
  let vss = add () tyc.c_pre tyc.c_post.t_vars in
  let vss = Mexn.fold add tyc.c_xpost vss in
  let check { vs_name = id } _ = if not (Mid.mem id varm) then
    Loc.errorm "Local variable %s escapes from its scope" id.id_string in
  Mvs.iter check vss;
  let result = filter_v varm vars tyc.c_result in
  let effect = eff_filter vars tyc.c_effect in
  { tyc with c_effect = effect; c_result = result }

let add_psymbol_spec varm ps tyv =
  let vars = Mid.fold (fun _ -> vars_union) varm vars_empty in
  let tyv = filter_v varm vars tyv in
  if Debug.test_flag debug then
    Format.eprintf "@[<hov 2>SPEC %a = %a@]@\n"
      Mlw_pretty.print_psty ps Mlw_pretty.print_type_v tyv;
  check_spec (VTarrow ps.ps_vta) tyv; (* TODO: prove and remove *)
  Wps.set psymbol_spec_t ps tyv

(* TODO? move spec_inst and subst to Mlw_expr? *)
let vtv_full_inst sbs vtv =
  vty_value ~ghost:vtv.vtv_ghost (ity_full_inst sbs vtv.vtv_ity)

let pv_full_inst sbs pv =
  create_pvsymbol (id_clone pv.pv_vs.vs_name) (vtv_full_inst sbs pv.pv_vtv)

let rec spec_inst_v sbs tvm vsm = function
  | SpecV vtv ->
      SpecV (vtv_full_inst sbs vtv)
  | SpecA (pvl,tyc) ->
      let add m pv =
        let nv = pv_full_inst sbs pv in
        Mvs.add pv.pv_vs (t_var nv.pv_vs) m, nv in
      let vsm, pvl = Util.map_fold_left add vsm pvl in
      SpecA (pvl, spec_inst_c sbs tvm vsm tyc)

and spec_inst_c sbs tvm vsm tyc =
  let subst = t_ty_subst tvm vsm in {
    c_pre    = subst tyc.c_pre;
    c_effect = eff_full_inst sbs tyc.c_effect;
    c_result = spec_inst_v sbs tvm vsm tyc.c_result;
    c_post   = subst tyc.c_post;
    c_xpost  = Mexn.map subst tyc.c_xpost; }

let rec subst_v pv t = function
  | SpecA (pvl,tyc) when not (List.exists (pv_equal pv) pvl) ->
      SpecA (pvl, subst_c pv t tyc)
  | tyv -> tyv

and subst_c pv t tyc =
  let subst = t_subst (Mvs.singleton pv.pv_vs t) in {
    c_pre    = subst tyc.c_pre;
    c_effect = tyc.c_effect;
    c_result = subst_v pv t tyc.c_result;
    c_post   = subst tyc.c_post;
    c_xpost  = Mexn.map subst tyc.c_xpost; }

let spec_lambda l tyv =
  let tyc = {
    c_pre    = l.l_pre;
    c_effect = l.l_expr.e_effect;
    c_result = tyv;
    c_post   = l.l_post;
    c_xpost  = l.l_xpost } in
  SpecA (l.l_args, tyc)

let spec_val vd = match vd.val_name with
  | LetA ps -> add_psymbol_spec vd.val_vars ps vd.val_spec
  | LetV _  -> ()

let rec spec_let { let_var = lv; let_expr = e } = match lv with
  | LetA ps -> add_psymbol_spec e.e_vars ps (spec_expr e)
  | LetV _  -> ignore (spec_expr e)

and spec_rec rdl =
  let add_vars m rd = Mid.set_union m rd.rec_vars in
  let vars = List.fold_left add_vars Mid.empty rdl in
  let add_early_spec rd = match rd.rec_lambda.l_expr.e_vty with
    | VTvalue vtv ->
        let tyv = spec_lambda rd.rec_lambda (SpecV vtv) in
        add_psymbol_spec rd.rec_vars rd.rec_ps tyv
    | VTarrow _ when Mid.mem rd.rec_ps.ps_name vars ->
        Loc.errorm ?loc:rd.rec_lambda.l_expr.e_loc
          "The body of a recursive function must be a first-order value"
    | VTarrow _ -> () in
  List.iter add_early_spec rdl;
  let add_late_spec rd =
    let tyv = spec_expr rd.rec_lambda.l_expr in
    match rd.rec_lambda.l_expr.e_vty with
    | VTarrow _ ->
        let tyv = spec_lambda rd.rec_lambda tyv in
        add_psymbol_spec rd.rec_vars rd.rec_ps tyv
    | VTvalue _ -> () in
  List.iter add_late_spec rdl

and spec_expr e = match e.e_node with
  | Elogic _
  | Eassert _
  | Eabsurd -> SpecV (vtv_of_expr e)
  | Evalue pv -> SpecV pv.pv_vtv
  | Earrow ps ->
    (* TODO: a ps may not be in the table, if it comes from a module
       for which we never computed WPs. Pass the known_map to spec_expr
       and compute it now. *)
      let sbs = vta_vars_match ps.ps_subst ps.ps_vta (vta_of_expr e) in
      let tvm = Mtv.map ty_of_ity sbs.ity_subst_tv in
      let tyv = Wps.find psymbol_spec_t ps in
      spec_inst_v sbs tvm Mvs.empty tyv
  | Eapp (e1,pv) ->
      let tyv = spec_expr e1 in
      let t = t_var pv.pv_vs in
      begin match tyv with
        | SpecA ([pv],tyc) ->
            let tyc = subst_c pv t tyc in
            (* we will use this for WP *)
            Wexpr.set e_apply_spec_t e tyc;
            tyc.c_result
        | SpecA (pv::pvl,tyc) ->
            (* pv cannot occur in pvl *)
            SpecA (pvl, subst_c pv t tyc)
        | _ -> assert false
      end
  | Elet (ld,e1) ->
      spec_let ld;
      spec_expr e1
  | Erec (rdl,e1) ->
      spec_rec rdl;
      spec_expr e1
  | Eghost e1 -> spec_expr e1
  | Eany tyc -> tyc.c_result
  | Eassign (e1,_,_)
  | Eloop (_,_,e1)
  | Efor (_,_,_,e1)
  | Eraise (_,e1)
  | Eabstr (e1,_,_) ->
      ignore (spec_expr e1);
      SpecV (vtv_of_expr e)
  | Eif (e1,e2,e3) ->
      ignore (spec_expr e1);
      ignore (spec_expr e2);
      spec_expr e3
  | Ecase (e1,bl) ->
      ignore (spec_expr e1);
      List.iter (fun (_,e) -> ignore (spec_expr e)) bl;
      SpecV (vtv_of_expr e)
  | Etry (e1,bl) ->
      ignore (spec_expr e1);
      List.iter (fun (_,_,e) -> ignore (spec_expr e)) bl;
      SpecV (vtv_of_expr e)

(** WP utilities *)

let fs_void = fs_tuple 0
let t_void = fs_app fs_void [] ty_unit

let ty_of_vty = function
  | VTvalue vtv -> ty_of_ity vtv.vtv_ity
  | VTarrow _   -> ty_unit

let default_exn_post xs _ =
  let vs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity) in
  create_post vs t_true

let default_post vty ef =
  let vs = create_vsymbol (id_fresh "result") (ty_of_vty vty) in
  create_post vs t_true, Mexn.mapi default_exn_post ef.eff_raises

let wp_label e f =
  let loc = if f.t_loc = None then e.e_loc else f.t_loc in
  let lab = Ident.Slab.union e.e_label f.t_label in
  t_label ?loc lab f

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:normal postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let expl_assert    = Ident.create_label "expl:assertion"
let expl_check     = Ident.create_label "expl:check"
let expl_loop_init = Ident.create_label "expl:loop invariant init"
let expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let expl_loop_var  = Ident.create_label "expl:loop variant decreases"
(* FIXME? couldn't we just reuse "loop invariant" explanations? *)
let expl_for_init  = Ident.create_label "expl:for loop initialization"
let expl_for_keep  = Ident.create_label "expl:for loop preservation"

let wp_expl l f =
  let lab = Slab.add Split_goal.stop_split f.t_label in
  t_label ?loc:f.t_loc (Slab.add l lab) f

let wp_and ~sym f1 f2 =
  if sym then t_and_simp f1 f2 else t_and_asym_simp f1 f2

let wp_ands ~sym fl =
  if sym then t_and_simp_l fl else t_and_asym_simp_l fl

let wp_implies f1 f2 = t_implies_simp f1 f2

let wp_let v t f = t_let_close_simp v t f

let wp_forall vl f = t_forall_close_simp vl [] f

let wp_forall_post v p f =
  (* we optimize for the case when a postcondition
     is of the form (... /\ result = t /\ ...) *)
  let rec down p = match p.t_node with
    | Tbinop (Tand,l,r) ->
        begin match down l with
          | None, _ ->
              let t, r = down r in
              t, t_label_copy p (t_and_simp l r)
          | t, l ->
              t, t_label_copy p (t_and_simp l r)
        end
    | Tapp (ps,[{t_node = Tvar u};t])
      when ls_equal ps ps_equ && vs_equal u v && not (Mvs.mem v t.t_vars) ->
        Some t, t_true
    | _ ->
        None, p
  in
  if ty_equal v.vs_ty ty_unit then
    t_subst_single v t_void (wp_implies p f)
  else match down p with
    | Some t, p -> wp_let v t (wp_implies p f)
    | _ -> wp_forall [v] (wp_implies p f)

let regs_of_reads  eff = Sreg.union eff.eff_reads eff.eff_ghostr
let regs_of_writes eff = Sreg.union eff.eff_writes eff.eff_ghostw
let regs_of_effect eff = Sreg.union (regs_of_reads eff) (regs_of_writes eff)
let exns_of_raises eff = Sexn.union eff.eff_raises eff.eff_ghostx

let open_unit_post q =
  let v, q = open_post q in
  t_subst_single v t_void q

let create_unit_post =
  let v = create_vsymbol (id_fresh "void") ty_unit in
  fun q -> create_post v q

let vs_result e =
  create_vsymbol (id_fresh ?loc:e.e_loc "result") (ty_of_vty e.e_vty)

(** WP state *)

type wp_env = {
  prog_known : Mlw_decl.known_map;
  pure_known : Decl.known_map;
  global_env : Env.env;
  ps_int_le  : Term.lsymbol;
  ps_int_ge  : Term.lsymbol;
  ps_int_lt  : Term.lsymbol;
  ps_int_gt  : Term.lsymbol;
  fs_int_pl  : Term.lsymbol;
}

let decrease ?loc env mk_old varl =
  let rec decr pr = function
    | [] -> t_false
    | { v_term = t; v_rel = rel }::varl ->
        let old_t = mk_old t in
        let d = match rel with
          | Some ls -> ps_app ls [t; old_t]
          | None when ty_equal (t_type t) ty_int ->
              t_and
                (ps_app env.ps_int_le [t_int_const "0"; old_t])
                (ps_app env.ps_int_lt [t; old_t])
          | None -> Loc.errorm ?loc
              "no default WF order for %a" Pretty.print_term t
        in
        let npr = t_and_simp pr (t_equ t old_t) in
        t_or_simp (t_and_simp pr d) (decr npr varl)
  in
  if varl = [] then t_true else decr t_true varl

(** Reconstruct pure values after writes *)

let find_constructors env sts ity = match ity.ity_node with
  | Itypur (ts,_) ->
      let base = ity_pur ts (List.map ity_var ts.ts_args) in
      let sbs = ity_match ity_subst_empty base ity in
      let csl = Decl.find_constructors env.pure_known ts in
      if csl = [] || Sts.mem ts sts then Loc.errorm
        "Cannot update values of type %a" Mlw_pretty.print_ity base;
      let subst ty = ity_full_inst sbs (ity_of_ty ty), None in
      let cnstr (cs,_) = cs, List.map subst cs.ls_args in
      Sts.add ts sts, List.map cnstr csl
  | Ityapp (its,_,_) ->
      let base = ity_app its (List.map ity_var its.its_args) its.its_regs in
      let sbs = ity_match ity_subst_empty base ity in
      let csl = Mlw_decl.find_constructors env.prog_known its in
      if csl = [] || Sts.mem its.its_pure sts then Loc.errorm
        "Cannot update values of type %a" Mlw_pretty.print_ity base;
      let subst vtv =
        ity_full_inst sbs vtv.vtv_ity,
        Util.option_map (reg_full_inst sbs) vtv.vtv_mut in
      let cnstr (cs,_) = cs.pl_ls, List.map subst cs.pl_args in
      Sts.add its.its_pure sts, List.map cnstr csl
  | Ityvar _ -> assert false

let update_var env mreg vs =
  let rec update sts vs ity mut =
    (* are we a mutable variable? *)
    let get_vs r = Mreg.find_def vs r mreg in
    let vs = Util.option_apply vs get_vs mut in
    (* should we update our value further? *)
    let check_reg r _ = reg_occurs r ity.ity_vars in
    if ity_pure ity || not (Mreg.exists check_reg mreg) then
      t_var vs
    else
      let sts, csl = find_constructors env sts ity in
      let branch (cs,ityl) =
        let mk_var (ity,_) = create_vsymbol (id_fresh "y") (ty_of_ity ity) in
        let vars = List.map mk_var ityl in
        let pat = pat_app cs (List.map pat_var vars) vs.vs_ty in
        let mk_arg vs (ity, mut) = update sts vs ity mut in
        let t = fs_app cs (List.map2 mk_arg vars ityl) vs.vs_ty in
        t_close_branch pat t in
      t_case (t_var vs) (List.map branch csl)
  in
  let vtv = vtv_of_vs vs in
  update Sts.empty vs vtv.vtv_ity vtv.vtv_mut

(* quantify over all references in eff
   eff : effect
   f   : formula

   let eff = { rho1, ..., rhon }
   we collect in vars all variables involving these regions
   let vars = { v1, ..., vm }

     forall r1:ty(rho1). ... forall rn:ty(rhon).
     let v'1 = update v1 r1...rn in
     ...
     let v'm = update vm r1...rn in
     f[vi <- v'i]
*)

let model1_lab = Slab.singleton (create_label "model:1")
let model2_lab = Slab.singleton (create_label "model:quantify(2)")
let model3_lab = Slab.singleton (create_label "model:cond")

let mk_var id label ty = create_vsymbol (id_clone ~label id) ty

let quantify env regs f =
  (* mreg : updated region -> vs *)
  let get_var reg () =
    let test vs _ id = match vtv_of_vs vs with
      | { vtv_ity = { ity_node = Ityapp (_,_,[r]) }}
      | { vtv_mut = Some r } when reg_equal r reg -> vs.vs_name
      | _ -> id in
    let id = Mvs.fold test f.t_vars reg.reg_name in
    mk_var id model1_lab (ty_of_ity reg.reg_ity)
  in
  let mreg = Mreg.mapi get_var regs in
  (* update all program variables involving these regions *)
  let update_var vs _ = match update_var env mreg vs with
    | { t_node = Tvar nv } when vs_equal vs nv -> None
    | t -> Some t in
  let vars = Mvs.mapi_filter update_var f.t_vars in
  (* vv' : old vs -> new vs *)
  let new_var vs _ = mk_var vs.vs_name model2_lab vs.vs_ty in
  let vv' = Mvs.mapi new_var vars in
  (* quantify *)
  let update v t f = wp_let (Mvs.find v vv') t f in
  let f = Mvs.fold update vars (drop_at true vv' f) in
  wp_forall (Mreg.values mreg) f

(** Weakest preconditions *)

let rec wp_expr env e q xq =
  (* FIXME? We only need to remove 'old from user-supplied posts.
     Therefore it suffices to do it for Erec, Eany, and Eabstr. *)
  let f = (* relativize ( *) wp_desc env e (* ) *) q xq in
  if Debug.test_flag debug then begin
    Format.eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Mlw_pretty.print_expr e;
    Format.eprintf "@[<hov 2>q = %a@]@\n" Pretty.print_term q;
    Format.eprintf "@[<hov 2>f = %a@]@\n----@]@." Pretty.print_term f;
  end;
  f

and wp_desc env e q xq = match e.e_node with
  | Elogic t ->
      let v, q = open_post q in
      let t = wp_label e t in
      (* NOTE: if you replace this t_subst by t_let or anything else,
         you must handle separately the case "let mark = 'now in ...",
         which requires 'now to be substituted for mark in q *)
      t_subst_single v (to_term t) q
  | Evalue pv ->
      let v, q = open_post q in
      let t = wp_label e (t_var pv.pv_vs) in
      t_subst_single v t q
  | Earrow _ ->
      let q = open_unit_post q in
      (* wp_label e *) q (* FIXME? *)
  | Elet ({ let_var = lv; let_expr = e1 }, e2) ->
      (* FIXME? Pgm_wp applies filter_post everywhere, but doesn't
         it suffice to do it only on Etry? The same question about
         saturate_post: why do we supply default exceptional posts
         instead of requiring an explicit xpost for every "raises"? *)
      let w = wp_expr env e2 q xq in
      let q = match lv with
        | LetV v -> create_post v.pv_vs w
        | LetA _ -> create_unit_post w in
      wp_label e (wp_expr env e1 q xq)
  | Erec (rdl, e) ->
      let fr = wp_rec_defn env rdl in
      let fe = wp_expr env e q xq in
      wp_and ~sym:true (wp_ands ~sym:true fr) fe
  | Eif (e1, e2, e3) ->
      let res = vs_result e1 in
      let test = t_equ (t_var res) t_bool_true in
      let test = t_label ?loc:e1.e_loc model3_lab test in
      (* if both branches are pure, do not split *)
      let w =
        let get_term e = match e.e_node with
          | Elogic t -> to_term t
          | Evalue v -> t_var v.pv_vs
          | _ -> raise Exit in
        try
          let r2 = get_term e2 in
          let r3 = get_term e3 in
          let v, q = open_post q in
          t_subst_single v (t_if_simp test r2 r3) q
        with Exit ->
          let w2 = wp_expr env e2 q xq in
          let w3 = wp_expr env e3 q xq in
          t_if_simp test w2 w3
      in
      let q = create_post res w in
      wp_label e (wp_expr env e1 q xq)
  (* optimization for the particular case let _ = e1 in e2 *)
  | Ecase (e1, [{ ppat_pattern = { pat_node = Term.Pwild }}, e2]) ->
      let w = wp_expr env e2 q xq in
      let q = create_post (vs_result e1) w in
      wp_label e (wp_expr env e1 q xq)
  (* optimization for the particular case let () = e1 in e2 *)
  | Ecase (e1, [{ ppat_pattern = { pat_node = Term.Papp (cs,[]) }}, e2])
    when ls_equal cs fs_void ->
      let w = wp_expr env e2 q xq in
      let q = create_unit_post w in
      wp_label e (wp_expr env e1 q xq)
  | Ecase (e1, bl) ->
      let res = vs_result e1 in
      let branch ({ ppat_pattern = pat }, e) =
        t_close_branch pat (wp_expr env e q xq) in
      let w = t_case (t_var res) (List.map branch bl) in
      let q = create_post res w in
      wp_label e (wp_expr env e1 q xq)
  | Eghost e1 ->
      wp_label e (wp_expr env e1 q xq)
  | Eraise (xs, e1) ->
      let q = try Mexn.find xs xq with
        Not_found -> assert false in
      wp_label e (wp_expr env e1 q xq)
  | Etry (e1, bl) ->
      let branch (xs,v,e) acc =
        let w = wp_expr env e q xq in
        let q = create_post v.pv_vs w in
        Mexn.add xs q acc in
      let xq = List.fold_right branch bl xq in
      wp_label e (wp_expr env e1 q xq)
  | Eassert (Aassert, f) ->
      let q = open_unit_post q in
      let f = wp_expl expl_assert f in
      wp_and ~sym:false (wp_label e f) q
  | Eassert (Acheck, f) ->
      let q = open_unit_post q in
      let f = wp_expl expl_check f in
      wp_and ~sym:true (wp_label e f) q
  | Eassert (Aassume, f) ->
      let q = open_unit_post q in
      wp_implies (wp_label e f) q
  | Eabsurd ->
      wp_label e t_absurd
  | Eany tyc ->
      let p = wp_label e (wp_expl expl_pre tyc.c_pre) in
      let p = t_label ?loc:e.e_loc p.t_label p in
      (* TODO: propagate call labels into tyc.c_post *)
      let w = wp_abstract env tyc.c_effect tyc.c_post tyc.c_xpost q xq in
      wp_and ~sym:false p w (* FIXME? do we need pre? *)
  | Eapp (e1,_) when Wexpr.mem e_apply_spec_t e ->
      let tyc = Wexpr.find e_apply_spec_t e in
      let p = wp_label e (wp_expl expl_pre tyc.c_pre) in
      let p = t_label ?loc:e.e_loc p.t_label p in
      (* TODO: propagate call labels into tyc.c_post *)
      let w = wp_abstract env tyc.c_effect tyc.c_post tyc.c_xpost q xq in
      let w = wp_and ~sym:false p w in (* FIXME? do we need pre? *)
      let q = create_unit_post w in
      wp_expr env e1 q xq (* FIXME? should (wp_label e) rather be here? *)
  | Eapp (e1,_) -> (* no effect, no pre, no post, no xpost *)
      let v, q = open_post q in
      let w = wp_forall [v] q in
      let q = create_unit_post w in
      wp_label e (wp_expr env e1 q xq)
  | Eabstr (e1, c_q, c_xq) ->
      let w1 = relativize (wp_expr env e1) c_q c_xq in
      let w2 = wp_abstract env e1.e_effect c_q c_xq q xq in
      wp_and ~sym:true (wp_label e w1) w2
  | Eassign (e1, reg, pv) ->
      let rec get_term d = match d.e_node with
        | Elogic t -> t
        | Evalue v -> t_var v.pv_vs
        | Eghost e | Elet (_,e) | Erec (_,e) -> get_term e
        | _ -> Loc.errorm ?loc:e.e_loc
            "Cannot compute the WP for this assignment"
      in
      let f = t_equ (get_term e1) (t_var pv.pv_vs) in
      let c_q = create_unit_post f in
      let eff = eff_write eff_empty reg in
      let w = wp_abstract env eff c_q Mexn.empty q xq in
      let q = create_post (vs_result e1) w in
      wp_label e (wp_expr env e1 q xq)
  | Eloop (inv, varl, e1) ->
      (* TODO: what do we do about well-foundness? *)
      let i = wp_expl expl_loop_keep inv in
      let d = decrease ?loc:e.e_loc env t_at_old varl in
      let q = create_unit_post (wp_and ~sym:true i d) in
      let w = relativize (wp_expr env e1) q xq in
      let regs = regs_of_writes e1.e_effect in
      let w = quantify env regs (wp_implies inv w) in
      let i = wp_expl expl_loop_init inv in
      wp_label e (wp_and ~sym:true i w)
  | Efor ({pv_vs = x}, ({pv_vs = v1}, d, {pv_vs = v2}), inv, e1) ->
      (* wp(for x = v1 to v2 do inv { I(x) } e1, Q, R) =
             v1 > v2  -> Q
         and v1 <= v2 ->     I(v1)
                         and forall S. forall i. v1 <= i <= v2 ->
                                                 I(i) -> wp(e1, I(i+1), R)
                                       and I(v2+1) -> Q *)
      let gt, le, incr = match d with
        | Mlw_expr.To     -> env.ps_int_gt, env.ps_int_le, t_int_const "1"
        | Mlw_expr.DownTo -> env.ps_int_lt, env.ps_int_ge, t_int_const "-1" in
      let v1_gt_v2 = ps_app gt [t_var v1; t_var v2] in
      let v1_le_v2 = ps_app le [t_var v1; t_var v2] in
      let q = open_unit_post q in
      let wp_init =
        wp_expl expl_for_init (t_subst_single x (t_var v1) inv) in
      let wp_step =
        let nextx = fs_app env.fs_int_pl [t_var x; incr] ty_int in
        let post = create_unit_post (t_subst_single x nextx inv) in
        wp_expr env e1 post xq in
      let wp_last =
        let v2pl1 = fs_app env.fs_int_pl [t_var v2; incr] ty_int in
        wp_implies (t_subst_single x v2pl1 inv) q in
      let wp_good = wp_and ~sym:true
        wp_init
        (quantify env (regs_of_writes e1.e_effect)
           (wp_and ~sym:true
              (wp_expl expl_for_keep (wp_forall [x] (wp_implies
                (wp_and ~sym:true (ps_app le [t_var v1; t_var x])
                                  (ps_app le [t_var x;  t_var v2]))
                (wp_implies inv wp_step))))
              wp_last))
      in
      let wp_full = wp_and ~sym:true
        (wp_implies v1_gt_v2 q)
        (wp_implies v1_le_v2 wp_good)
      in
      wp_label e wp_full

and wp_abstract env c_eff c_q c_xq q xq =
  let regs = regs_of_writes c_eff in
  let exns = exns_of_raises c_eff in
  let quantify_post c_q q =
    let v, f = open_post q in
    let c_v, c_f = open_post c_q in
    let c_f = t_subst_single c_v (t_var v) c_f in
    let f = wp_forall_post v c_f f in
    quantify env regs f
  in
  let quantify_xpost _ c_xq xq =
    Some (quantify_post c_xq xq) in
  let proceed c_q c_xq =
    let f = quantify_post c_q q in
    (* every xs in exns is guaranteed to be in c_xq and xq *)
    assert (Mexn.set_submap exns xq);
    assert (Mexn.set_submap exns c_xq);
    let xq = Mexn.set_inter xq exns in
    let c_xq = Mexn.set_inter c_xq exns in
    let mexn = Mexn.inter quantify_xpost c_xq xq in
    wp_ands ~sym:true (f :: Mexn.values mexn)
  in
  relativize proceed c_q c_xq

and wp_lambda env l =
  let q = wp_expl expl_post l.l_post in
  let xq = Mexn.map (wp_expl expl_xpost) l.l_xpost in
  let f = relativize (wp_expr env l.l_expr) q xq in
  let f = wp_implies l.l_pre f in
  let f = quantify env (regs_of_effect l.l_expr.e_effect) f in
  wp_forall (List.map (fun pv -> pv.pv_vs) l.l_args) f

and wp_rec_defn env rdl =
  List.map (fun rd -> wp_lambda env rd.rec_lambda) rdl

(***
let bool_to_prop env f =
  let ts_bool  = find_ts ~pure:true env "bool" in
  let ls_andb  = find_ls ~pure:true env "andb" in
  let ls_orb   = find_ls ~pure:true env "orb" in
  let ls_notb  = find_ls ~pure:true env "notb" in
  let ls_True  = find_ls ~pure:true env "True" in
  let ls_False = find_ls ~pure:true env "False" in
  let t_True   = fs_app ls_True [] (ty_app ts_bool []) in
  let is_bool ls = ls_equal ls ls_True || ls_equal ls ls_False in
  let rec t_iff_bool f1 f2 = match f1.t_node, f2.t_node with
    | Tnot f1, _ -> t_not_simp (t_iff_bool f1 f2)
    | _, Tnot f2 -> t_not_simp (t_iff_bool f1 f2)
    | Tapp (ps1, [t1; { t_node = Tapp (ls1, []) }]),
      Tapp (ps2, [t2; { t_node = Tapp (ls2, []) }])
      when ls_equal ps1 ps_equ && ls_equal ps2 ps_equ &&
           is_bool ls1 && is_bool ls2 ->
        if ls_equal ls1 ls2 then t_equ t1 t2 else t_neq t1 t2
    | _ ->
        t_iff_simp f1 f2
  in
  let rec t_btop t = t_label ?loc:t.t_loc t.t_label (* t_label_copy? *)
    (match t.t_node with
    | Tif (f,t1,t2) ->
        t_if_simp (f_btop f) (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_andb ->
        t_and_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1;t2]) when ls_equal ls ls_orb ->
        t_or_simp (t_btop t1) (t_btop t2)
    | Tapp (ls, [t1]) when ls_equal ls ls_notb ->
        t_not_simp (t_btop t1)
    | Tapp (ls, []) when ls_equal ls ls_True ->
        t_true
    | Tapp (ls, []) when ls_equal ls ls_False ->
        t_false
    | _ ->
        t_equ_simp (f_btop t) t_True)
  and f_btop f = match f.t_node with
    | Tapp (ls, [{t_ty = Some {ty_node = Tyapp (ts, [])}} as l; r])
      when ls_equal ls ps_equ && ts_equal ts ts_bool ->
        t_label ?loc:f.t_loc f.t_label (t_iff_bool (t_btop l) (t_btop r))
    | _ ->
        t_map_simp f_btop f
  in
  f_btop f
***)

(* replace t_absurd with t_false *)
let rec unabsurd f = match f.t_node with
  | Tapp (ls, []) when ls_equal ls ls_absurd ->
      t_label_copy f t_false
  | _ ->
      t_map unabsurd f

let add_wp_decl name f uc =
  (* prepare a proposition symbol *)
  let s = "WP_" ^ name.id_string in
  let lab = Ident.create_label ("expl:" ^ name.id_string) in
  let label = Slab.add lab name.id_label in
  let id = id_fresh ~label ?loc:name.id_loc s in
  let pr = create_prsymbol id in
  (* prepare the VC formula *)
  (* let f = remove_at f in (* FIXME: do we need this? *) *)
  (* let f = bool_to_prop uc f in *)
  let f = unabsurd f in
  (* get a known map with tuples added *)
  let km = Theory.get_known uc in
  (* simplify f *)
  let f = Eval_match.eval_match ~inline:Eval_match.inline_nonrec_linear km f in
  (* printf "wp: f=%a@." print_term f; *)
  let d = create_prop_decl Pgoal pr f in
  Theory.add_decl uc d

let mk_env env km th =
  let th_int = Env.find_theory env ["int"] "Int" in
  { prog_known = km;
    pure_known = Theory.get_known th;
    global_env = env;
    ps_int_le  = Theory.ns_find_ls th_int.th_export ["infix <="];
    ps_int_ge  = Theory.ns_find_ls th_int.th_export ["infix >="];
    ps_int_lt  = Theory.ns_find_ls th_int.th_export ["infix <"];
    ps_int_gt  = Theory.ns_find_ls th_int.th_export ["infix >"];
    fs_int_pl  = Theory.ns_find_ls th_int.th_export ["infix +"];
  }

let wp_let env km th ({ let_var = lv; let_expr = e } as ld) =
  spec_let ld;
  let env = mk_env env km th in
  let q, xq = default_post e.e_vty e.e_effect in
  let f = wp_expr env e q xq in
  let f = wp_forall (Mvs.keys f.t_vars) f in
  let id = match lv with
    | LetV pv -> pv.pv_vs.vs_name
    | LetA ps -> ps.ps_name in
  add_wp_decl id f th

let wp_rec env km th rdl =
  spec_rec rdl;
  let env = mk_env env km th in
  let fl = wp_rec_defn env rdl in
  let add_one th d f =
    Debug.dprintf debug "wp %s = %a@\n----------------@."
      d.rec_ps.ps_name.id_string Pretty.print_term f;
    let f = wp_forall (Mvs.keys f.t_vars) f in
    add_wp_decl d.rec_ps.ps_name f th
  in
  List.fold_left2 add_one th rdl fl

let wp_val _env _km th vd = spec_val vd; th
