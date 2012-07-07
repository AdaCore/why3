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

let fresh_mark () = create_vsymbol (id_fresh "mark") ty_mark

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let th_mark =
  let uc = create_theory (id_fresh "WP builtins") in
  let uc = add_ty_decl uc ts_mark in
  let uc = add_param_decl uc fs_at in
  let uc = add_param_decl uc fs_old in
  close_theory uc

let fs_setmark =
  create_lsymbol (id_fresh "set_mark") [] (Some ty_mark)

let e_setmark = e_lapp fs_setmark [] (ity_pur ts_mark [])

let vs_old = create_vsymbol (id_fresh "'old") ty_mark
let vs_now = create_vsymbol (id_fresh "'now") ty_mark

let ls_absurd = create_lsymbol (id_fresh "absurd") [] None
let t_absurd  = ps_app ls_absurd []
let mk_t_if f = t_if f t_bool_true t_bool_false

(* replace [at(t,'old)] with [at(t,lab)] everywhere in formula [f] *)
let old_mark lab t = t_subst_single vs_old (t_var lab) t

(* replace [at(t,lab)] with [at(t,'now)] everywhere in formula [f] *)
let erase_mark lab t = t_subst_single lab (t_var vs_now) t

(* replace [at(t,now)] with [t] modulo variable renaming *)
let rec drop_at now m t = match t.t_node with
  | Tvar vs when now ->
      begin try t_var (Mvs.find vs m) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls fs_old ->
      assert false
  | Tapp (ls, [e;{t_node = Tvar lab}]) when ls_equal ls fs_at ->
      if vs_equal lab vs_old then assert false else
      if vs_equal lab vs_now then drop_at true m e else
      (* no longer assume that unmarked variables are at mark 'now *)
      t_map (drop_at false m) t
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      (* do not open unless necessary *)
      let m = Mvs.set_inter m t.t_vars in
      if Mvs.is_empty m then t else
      t_map (drop_at now m) t
  | _ ->
      t_map (drop_at now m) t

(** Specifications *)

let psymbol_spec_t : type_v Wps.t = Wps.create 17

let add_pv_varm pv m = Mid.add pv.pv_vs.vs_name pv.pv_vtv.vtv_vars m
let add_pv_vars pv s = vars_union pv.pv_vtv.vtv_vars s

let check_spec ps tyv =
  let rec check vty tyv = match vty, tyv with
    | VTvalue _, SpecV _ -> ()
    | VTarrow vta, SpecA (_::(_::_ as pvl), tyc) ->
        assert (eff_is_empty vta.vta_effect);
        check vta.vta_result (SpecA (pvl, tyc))
    | VTarrow vta, SpecA ([_], tyc) ->
        let eff1 = vta.vta_effect in
        let eff2 = tyc.c_effect in
        assert (Sreg.equal eff1.eff_reads  eff2.eff_reads);
        assert (Sreg.equal eff1.eff_writes eff2.eff_writes);
        assert (Sexn.equal eff1.eff_raises eff2.eff_raises);
        assert (Sreg.equal eff1.eff_ghostr eff2.eff_ghostr);
        assert (Sreg.equal eff1.eff_ghostw eff2.eff_ghostw);
        assert (Sexn.equal eff1.eff_ghostx eff2.eff_ghostx);
        check vta.vta_result tyc.c_result
    | _ -> assert false
  in
  check (VTarrow ps.ps_vta) tyv

let rec filter_v ~strict varm vars = function
  | SpecA (pvl, tyc) ->
      let varm = List.fold_right add_pv_varm pvl varm in
      let vars = List.fold_right add_pv_vars pvl vars in
      SpecA (pvl, filter_c ~strict varm vars tyc)
  | tyv -> tyv

and filter_c ~strict varm vars tyc =
  let result = filter_v ~strict varm vars tyc.c_result in
  let effect = eff_filter vars tyc.c_effect in
  if strict then begin
    let add _ f s = Mvs.set_union f.t_vars s in
    let vss = add () tyc.c_pre tyc.c_post.t_vars in
    let vss = Mexn.fold add tyc.c_xpost vss in
    let check { vs_name = id } _ = if not (Mid.mem id varm) then
      Loc.errorm "Local variable %s escapes from its scope" id.id_string in
    Mvs.iter check vss
  end;
  { tyc with c_effect = effect; c_result = result }

let spec_lambda l tyv =
  let tyc = {
    c_pre    = l.l_pre;
    c_effect = l.l_expr.e_effect;
    c_result = tyv;
    c_post   = l.l_post;
    c_xpost  = l.l_xpost } in
  SpecA (l.l_args, tyc)

let spec_val { val_name = lv; val_spec = tyv } = match lv with
  | LetA ps when not (Wps.mem psymbol_spec_t ps) ->
      check_spec ps tyv; (* TODO: remove *)
      Wps.set psymbol_spec_t ps tyv
  | _ -> ()

let rec spec_let ~strict { let_var = lv; let_expr = e } = match lv with
  | LetA ps when not (Wps.mem psymbol_spec_t ps) ->
    (* FIXME: memoization is broken if one declares the same psymbol
       both as a local (non-strict) let and as a global (strict) let.
       First global, then local is safe. First local, then global
       may lead to an escaping variable, which will or will not
       be detected by the core API. *)
      let vars = Mid.fold (fun _ -> vars_union) e.e_vars vars_empty in
      let tyv = filter_v ~strict e.e_vars vars (spec_expr e) in
      check_spec ps tyv; (* TODO: remove *)
      Wps.set psymbol_spec_t ps tyv
  | _ -> ()

and spec_rec rdl =
  let add_vars m rd = Mid.set_union m rd.rec_vars in
  let vars = List.fold_left add_vars Mid.empty rdl in
  let add_early_spec rd = match rd.rec_lambda.l_expr.e_vty with
    | VTvalue vtv ->
        let tyv = spec_lambda rd.rec_lambda (SpecV vtv) in
        check_spec rd.rec_ps tyv; (* TODO: remove *)
        Wps.set psymbol_spec_t rd.rec_ps tyv
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
        check_spec rd.rec_ps tyv; (* TODO: remove *)
        Wps.set psymbol_spec_t rd.rec_ps tyv
    | VTvalue _ -> () in
  List.iter add_late_spec rdl

and spec_expr e = match e.e_node with
  | Elogic _
  | Eassert _
  | Eabsurd -> SpecV (vtv_of_expr e)
  | Evalue pv -> SpecV pv.pv_vtv
  | Earrow ps -> Wps.find psymbol_spec_t ps
      (* TODO: a ps may not be in the table, if it comes from a module
         for which we never computed WPs. Pass the known_map to spec_expr
         and compute it now. *)
  | Eapp (_, _) ->
      assert false (* TODO *)
  | Elet (ld,e1) -> spec_let ~strict:false ld; spec_expr e1
  | Erec (rdl,e1) -> spec_rec rdl; spec_expr e1
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

let wp_expl l f =
  let lab = Slab.add Split_goal.stop_split f.t_label in
  let lab = Slab.add (Ident.create_label ("expl:" ^ l)) lab in
  t_label ?loc:f.t_loc lab f

let wp_and ?(sym=false) f1 f2 =
  if sym then t_and_simp f1 f2 else t_and_asym_simp f1 f2

let wp_ands ?(sym=false) fl =
  if sym then t_and_simp_l fl else t_and_asym_simp_l fl

let wp_implies f1 f2 = t_implies_simp f1 f2

let wp_forall vl f = t_forall_close_simp vl [] f

let wp_let v t f = t_let_close_simp v t f

(*
match f.t_node with
  | Tbinop (Timplies, {t_node = Tapp (s,[{t_node = Tvar u};r])},h)
    when ls_equal s ps_equ && vs_equal u v && not (Mvs.mem v r.t_vars) ->
      t_let_close_simp v r h
  | Tbinop (Timplies, {t_node = Tbinop (Tand, g,
                      {t_node = Tapp (s,[{t_node = Tvar u};r])})},h)
    when ls_equal s ps_equ && vs_equal u v && not (Mvs.mem v r.t_vars) ->
      t_let_close_simp v r (t_implies_simp g h)
  | _ when Mvs.mem v f.t_vars ->
      t_forall_close_simp [v] [] f
  | _ ->
      f
*)

(** WP state *)

type wp_env = {
  prog_known : Mlw_decl.known_map;
  pure_known : Decl.known_map;
  global_env : Env.env;
}

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
  let vtv = (restore_pv vs).pv_vtv in
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
let mk_var id label ty = create_vsymbol (id_clone ~label id) ty

let quantify env regs f =
  (* mreg : updated region -> vs *)
  let get_var reg () =
    let test vs _ id = match (restore_pv vs).pv_vtv with
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

let regs_of_reads  eff = Sreg.union eff.eff_reads eff.eff_ghostr
let regs_of_writes eff = Sreg.union eff.eff_writes eff.eff_ghostw
let regs_of_effect eff = Sreg.union (regs_of_reads eff) (regs_of_writes eff)

let rec wp_expr env e q xq =
  let lab = fresh_mark () in
  let q = old_mark lab q in
  let xq = Mexn.map (old_mark lab) xq in
  let f = wp_desc env e q xq in
  let f = erase_mark lab f in
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
      let t = if t.t_ty = None then mk_t_if t else t in
      t_subst_single v t q
  | Evalue pv ->
      let v, q = open_post q in
      let t = wp_label e (t_var pv.pv_vs) in
      t_subst_single v t q
  | Erec (rdl, e) ->
      let fr = wp_rec_defn env rdl in
      let fe = wp_expr env e q xq in
      wp_and ~sym:true (wp_ands ~sym:true fr) fe
  | Eabsurd ->
      wp_label e t_absurd

  |Earrow _-> assert false
  |Eassert (_, _)-> assert false
  |Eabstr (_, _, _)-> assert false
  |Etry (_, _)-> assert false
  |Eraise (_, _)-> assert false
  |Efor (_, _, _, _)-> assert false
  |Eloop (_, _, _)-> assert false
  |Eany _-> assert false
  |Eghost _-> assert false
  |Eassign (_, _, _)-> assert false
  |Ecase (_, _)-> assert false
  |Eif (_, _, _)-> assert false
  |Elet (_, _)-> assert false
  |Eapp (_, _)-> assert false

and wp_lambda env l =
  let q = wp_expl "normal postcondition" l.l_post in
  let xq = Mexn.map (wp_expl "exceptional postcondition") l.l_xpost in
  let f = wp_expr env l.l_expr q xq in
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

(* replace every occurrence of [at(t,'now)] with [t] *)
let rec remove_at f = match f.t_node with
  | Tapp (ls, [t;{t_node = Tvar lab}])
    when ls_equal ls fs_at && vs_equal lab vs_now ->
      remove_at t
  | _ ->
      t_map remove_at f

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
  let f = remove_at f in
  (* let f = bool_to_prop uc f in *)
  let f = unabsurd f in
  (* get a known map with tuples added *)
  let km = Theory.get_known uc in
  (* simplify f *)
  let f = Eval_match.eval_match ~inline:Eval_match.inline_nonrec_linear km f in
  (* printf "wp: f=%a@." print_term f; *)
  let d = create_prop_decl Pgoal pr f in
  Theory.add_decl uc d

let mk_env env km th = {
  prog_known = km;
  pure_known = Theory.get_known th;
  global_env = env;
}

let wp_let env km th ({ let_var = lv; let_expr = e } as ld) =
  spec_let ~strict:true ld;
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
    add_wp_decl d.rec_ps.ps_name f th
  in
  List.fold_left2 add_one th rdl fl

let wp_val _env _km th vd = spec_val vd; th
