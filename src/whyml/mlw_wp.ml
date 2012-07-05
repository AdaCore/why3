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

(** WP-only builtins *)

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

(** Weakest preconditions *)

let ty_of_vty = function
  | VTvalue vtv -> ty_of_ity vtv.vtv_ity
  | VTarrow _   -> ty_unit

let default_exn_post xs _ =
  let vs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity) in
  create_post vs t_true

let default_post vty ef =
  let vs = create_vsymbol (id_fresh "result") (ty_of_vty vty) in
  create_post vs t_true,
  Mexn.mapi default_exn_post ef.eff_raises

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

let wp_implies f1 f2 = match f2.t_node with
  | Tfalse -> t_implies f1 f2
  | _ -> t_implies_simp f1 f2

let wp_forall v f =
  (* if t_occurs_single v f then t_forall_close_simp [v] [] f else f *)
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

let wp_binder x f = wp_forall x.pv_vs f
let wp_binders = List.fold_right wp_binder

let wp_close_state _km _lkm _ef f =
  f (* TODO *)

let rec wp_expr km lkm e q xq =
  let lab = fresh_mark () in
  let q = old_mark lab q in
  let xq = Mexn.map (old_mark lab) xq in
  let tyv, f = wp_desc km lkm e q xq in
  let f = erase_mark lab f in
  if Debug.test_flag debug then begin
    (* eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Mlw_pretty.print_expr e; *)
    Format.eprintf "@[<hov 2>q = %a@]@\n" Pretty.print_term q;
    Format.eprintf "@[<hov 2>f = %a@]@\n----@]@." Pretty.print_term f;
  end;
  tyv, f

and wp_desc km lkm e q xq = match e.e_node with
  | Eabsurd ->
      SpecV (vtv_of_expr e), wp_label e t_absurd
  | Erec (rdl, e) ->
      let fr = wp_rec_defn km lkm rdl in
      let tyv, fe = wp_expr km lkm e q xq in
      tyv, wp_and ~sym:true (wp_ands ~sym:true fr) fe
  | Elogic t ->
      let v, q = open_post q in
      let t = wp_label e t in
      let t = if t.t_ty = None then mk_t_if t else t in
      SpecV (vtv_of_expr e), t_subst_single v t q
  | Earrow _-> assert false
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
  |Evalue _ -> assert false (*TODO*)

and wp_lambda km lkm l =
  let q = wp_expl "normal postcondition" l.l_post in
  let xq = Mexn.map (wp_expl "exceptional postcondition") l.l_xpost in
  let tyv, f = wp_expr km lkm l.l_expr q xq in
  let f = wp_implies l.l_pre f in
  let f = wp_close_state km lkm l.l_expr.e_effect f in
  let tyc = { c_pre = l.l_pre; c_effect = l.l_expr.e_effect;
              c_result = tyv; c_post = l.l_post; c_xpost = l.l_xpost } in
  SpecA (l.l_args, tyc), wp_binders l.l_args f

and wp_rec_defn km lkm rdl =
  (* TODO: fill the table with type_v for the recursive functions *)
  let rec_defn d = snd (wp_lambda km lkm d.rec_lambda) in
  List.map rec_defn rdl

let wp km lkm e =
  let q, xq = default_post e.e_vty e.e_effect in
  let _, f = wp_expr km lkm e q xq in
  let vl = Mvs.keys f.t_vars in
  t_forall_close vl [] f

let wp_val _km th _lv =
  th

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

let wp_let km th ld =
  let f = wp km (Theory.get_known th) ld.let_expr in
  let id = match ld.let_var with
    | LetV pv -> pv.pv_vs.vs_name | LetA ps -> ps.ps_name
  in
  add_wp_decl id f th

let wp_rec km th rdl =
  let fl = wp_rec_defn km (Theory.get_known th) rdl in
  let add_one th d f =
    let id = d.rec_ps.ps_name in
    Debug.dprintf debug "wp %s = %a@\n----------------@."
      id.id_string Pretty.print_term f;
    add_wp_decl id f th
  in
  List.fold_left2 add_one th rdl fl

