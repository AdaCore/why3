(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Format
open Why
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Pretty
open Pgm_ttree
open Pgm_env

module E = Pgm_effect

let debug = ref false

(* phase 4: weakest preconditions *******************************************)

(* smart constructors for building WPs
   TODO: use simp forms / tag with label "WP" *)

let wp_and ?(sym=false) f1 f2 = 
(*   if sym then f_and_simp f1 f2 else f_and_simp f1 (f_implies_simp f1 f2)  *)
  let f = f_and_simp f1 f2 in
  if sym then f else f_label [Split_goal.asym_split] f

let wp_ands ?(sym=false) fl =
  List.fold_left (wp_and ~sym) f_true fl

let wp_implies = f_implies_simp
let wp_forall  = f_forall_simp

(* utility functions for building WPs *)

let fresh_label env =
  let ty = ty_app env.ts_label [] in
  create_vsymbol (id_fresh "label") ty

let wp_binder (x, tv) f = match tv with
  | Tpure _ -> wp_forall [x] [] f
  | Tarrow _ -> f

let wp_binders = List.fold_right wp_binder 

(* replace old(t) with at(t,lab) everywhere in formula f *)
let rec old_label env lab f =
  f_map (old_label_term env lab) (old_label env lab) f

and old_label_term env lab t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls env.ls_old ->
      let t = old_label_term env lab t in (* NECESSARY? *)
      t_app env.ls_at [t; t_var lab] t.t_ty
  | _ ->
      t_map (old_label_term env lab) (old_label env lab) t

(* replace at(t,lab) with t everywhere in formula f *)
let rec erase_label env lab f =
  f_map (erase_label_term env lab) (erase_label env lab) f

and erase_label_term env lab t = match t.t_node with
  | Tapp (ls, [t; {t_node = Tvar l}]) 
    when ls_equal ls env.ls_at && vs_equal l lab ->
      erase_label_term env lab t
  | _ ->
      t_map (erase_label_term env lab) (erase_label env lab) t

let unref_ty env ty = match ty.ty_node with
  | Tyapp (ts, [ty]) when ts_equal ts env.ts_ref -> ty
  | _ -> assert false

let is_ref_ty env ty = match ty.ty_node with
  | Tyapp (ts, [_]) -> ts_equal ts env.ts_ref
  | _ -> false

(* replace !r by v everywhere in formula f *)
let rec unref env r v f =
  f_map (unref_term env r v) (unref env r v) f

and unref_term env r v t = match t.t_node with
  | Tapp (ls, [u]) when ls_equal ls env.ls_bang ->
      let rt = E.reference_of_term u in
      if E.ref_equal rt r then t_var v else t
  | Tapp (ls, _) when ls_equal ls env.ls_old ->
      assert false
  | Tapp (ls, _) when ls_equal ls env.ls_at -> (* do not recurse in at(...) *)
      t 
  | _ ->
      t_map (unref_term env r v) (unref env r v) t

(* quantify over all references in ef *)
let quantify ?(all=false) env ef f =
  (* eprintf "quantify: ef=%a f=%a@." E.print ef Pretty.print_fmla f; *)
  let quantify1 r f = 
    let ty = unref_ty env (E.type_of_reference r) in
    let v = create_vsymbol (id_clone (E.name_of_reference r)) ty in
    let f = unref env r v f in
    wp_forall [v] [] f
  in
  let s = ef.E.writes in
  let s = if all then E.Sref.union ef.E.reads s else s in
  E.Sref.fold quantify1 s f

let abstract_wp env ef (q',ql') (q,ql) =
  assert (List.length ql' = List.length ql);
  let quantify_res f' f res =
    let f = wp_implies f' f in
    let f = match res with 
      | Some v when is_ref_ty env v.vs_ty -> 
	  let v' = create_vsymbol (id_clone v.vs_name) (unref_ty env v.vs_ty) in
	  wp_forall [v'] [] (unref env (E.Rlocal v) v' f)
      | Some v -> 
	  wp_forall [v] [] f
      | None -> 
	  f 
    in
    quantify env ef f
  in
  let quantify_h (e',(x',f')) (e,(x,f)) =
    assert (ls_equal e' e);
    let res, f' = match x', x with
      | Some v', Some v -> Some v, f_subst (subst1 v' (t_var v)) f'
      | None, None -> None, f'
      | _ -> assert false
    in
    quantify_res f' f res
  in
  let f = 
    let res, f = q and res', f' = q' in
    let f' = f_subst (subst1 res' (t_var res)) f' in
    quantify_res f' f (Some res)
  in
  wp_ands (f :: List.map2 quantify_h ql' ql)

let opaque_wp env ef q' q = 
  let lab = fresh_label env in
  let q' = post_map (old_label env lab) q' in
  let f = abstract_wp env ef q' q in
  erase_label env lab f

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in effect [ef] *)

let filter_post ef (q, ql) =
  let keep (ls, _) = Sls.mem ls ef.E.raises in
  q, List.filter keep ql

let rec ls_assoc ls = function
  | [] -> raise Not_found
  | (ls', x) :: _ when ls_equal ls ls' -> x
  | _ :: r -> ls_assoc ls r

let exn_v_result ls = match ls.ls_args with
  | [] -> None
  | [ty] -> Some (v_result ty)
  | _ -> assert false

let default_exn_post ls = ls, (exn_v_result ls, f_true)

let default_post ty ef =
  (v_result ty, f_true), 
  List.map default_exn_post (Sls.elements ef.E.raises)

let rec assoc_handler x = function
  | [] -> assert false
  | (y, h) :: _ when ls_equal x y -> h
  | _ :: hl -> assoc_handler x hl

(*s [saturate_post ef f q] makes a postcondition for a program of effect [ef]
    out of a normal postcondition [f] and the exc. postconditions from [q] *)

let saturate_post ef q (_, ql) = 
  let set_post x = try x, ls_assoc x ql with Not_found -> default_exn_post x in
  let xs = Sls.elements ef.E.raises in
  (q, List.map set_post xs)

(* maximum *)

let is_default_post = f_equal f_true

let sup ((q, ql) : post) (_, ql') =
  assert (List.length ql = List.length ql');
  let supx (x, (_,fa) as a) (x', _ as a') =
    assert (ls_equal x x');
    if is_default_post fa then a' else a
  in
  q, List.map2 supx ql ql' 

(* post-condition for a loop body *)

let default_exns_post ef =
  let xs = Sls.elements ef.E.raises in
  List.map default_exn_post xs
 
let term_at env lab t =
  t_app env.ls_at [t; t_var lab] t.t_ty

let while_post_block env inv var lab e = 
  let decphi = match var with
    | None -> 
	f_true
    | Some (phi, r) -> 
	f_app r [phi; term_at env lab phi]
  in
  let ql = default_exns_post e.expr_effect in
  let res = v_result e.expr_type in
  match inv with
    | None -> 
	(res, decphi), ql
    | Some i -> 
	(res, wp_and i decphi), ql

let well_founded_rel = function
  | None -> f_true
  | Some (_,_r) -> f_true (* TODO: Papp (well_founded, [Tvar r], []) *)


(* Recursive computation of the weakest precondition *)

let rec wp_expr env e q = 
  (* if !debug then  *)
  (*   eprintf "@[wp_expr: q=%a@]@." Pretty.print_fmla (snd (fst q)); *)
  let lab = fresh_label env in
  let q = post_map (old_label env lab) q in
  let f = wp_desc env e q in
  erase_label env lab f

and wp_desc env e q = match e.expr_desc with
  | Elogic t ->
      let (v, q), _ = q in
      f_let v t q
  | Elocal v ->
      let (res, q), _ = q in
      f_subst (subst1 res (t_var v)) q
  | Eglobal _ ->
      let (_, q), _ = q in q
  | Efun (bl, t) ->
      let (_, q), _ = q in
      let f = wp_triple env t in
      wp_and q (wp_binders bl f)
  | Elet (x, e1, e2) ->
      let w2 = wp_expr env e2 (filter_post e2.expr_effect q) in
      let result = v_result e1.expr_type in
      let q1 = result, f_subst (subst1 x (t_var result)) w2 in
      let q1 = saturate_post e1.expr_effect q1 q in
      wp_expr env e1 q1
  | Eletrec (dl, e1) ->
      let w1 = wp_expr env e1 q in
      let wl = List.map (wp_recfun env) dl in 
      wp_ands ~sym:true (w1 :: wl)

  | Esequence (e1, e2) ->
      let w2 = wp_expr env e2 (filter_post e2.expr_effect q) in
      let q1 = saturate_post e1.expr_effect (v_result e1.expr_type, w2) q in
      wp_expr env e1 q1
  | Eif (e1, e2, e3) ->
      let w2 = wp_expr env e2 (filter_post e2.expr_effect q) in
      let w3 = wp_expr env e3 (filter_post e3.expr_effect q) in
      let q1 = (* if result=True then w2 else w3 *)
	let res = v_result e1.expr_type in
	let test = f_equ (t_var res) (t_True env) in
	let q1 = f_if test w2 w3 in
	saturate_post e1.expr_effect (res, q1) q
      in
      wp_expr env e1 q1
  | Eloop ({ loop_invariant = inv; loop_variant = var }, e1) ->
      let wfr = well_founded_rel var in
      let lab = fresh_label env in
      let q1 = while_post_block env inv var lab e1 in
      let q1 = sup q1 q in (* exc. posts taken from [q] *)
      let we = wp_expr env e1 q1 in
      let we = erase_label env lab we in
      let w = match inv with
	| None ->
	    wp_and wfr (quantify env e.expr_effect we)
	| Some i ->
	    wp_and wfr
	      (wp_and ~sym:true
		 i
		 (quantify env e.expr_effect (wp_implies i we)))
	in
	w
  | Ematch (x, bl) ->
      let branch (p, e) = p, wp_expr env e (filter_post e.expr_effect q) in
      let t = t_var x in
      f_case t (List.map branch bl)
  | Eskip ->
      let (_, q), _ = q in q
  | Eabsurd ->
      f_false
  | Eraise (x, None) ->
      (* $wp(raise E, _, R) = R$ *)
      let _, ql = q in
      let _, f = assoc_handler x ql in f
  | Eraise (x, Some e1) ->
      (* $wp(raise (E e1), _, R) = wp(e1, R, R)$ *)
      let _, ql = q in
      let q1 = match assoc_handler x ql with
	| Some v, r -> (v, r), ql 
	| None, _ -> assert false
      in
      let q1 = filter_post e1.expr_effect q1 in
      wp_expr env e1 q1
  | Etry (e1, hl) ->
      (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
      let hwl = 
	List.map 
	  (fun (x, v, h) -> 
	     let w = wp_expr env h (filter_post h.expr_effect q) in
	     x, (v, w))
	  hl 
      in
      let make_post (q, ql) =
	let hpost (x, r) =
	  x, try assoc_handler x hwl with Not_found -> r
	in
	q, List.map hpost ql
      in
      let q1 = saturate_post e1.expr_effect (fst q) q in
      let q1 = filter_post e1.expr_effect (make_post q1) in
      wp_expr env e1 q1

  | Eassert (Pgm_ptree.Aassert, f) ->
      let (_, q), _ = q in
      wp_and f q
  | Eassert (Pgm_ptree.Acheck, f) ->
      let (_, q), _ = q in
      wp_and ~sym:true f q
  | Eassert (Pgm_ptree.Aassume, f) ->
      let (_, q), _ = q in
      wp_implies f q
  | Elabel (lab, e1) ->
      let w1 = wp_expr env e1 q in
      erase_label env lab w1
  | Eany c ->
      let w = opaque_wp env c.c_effect c.c_post q in
      wp_and c.c_pre w

  | Eghost _ ->
      assert false (*TODO*)

and wp_triple env (p, e, q) =
  let f = wp_expr env e q in
  let f = wp_implies p f in
  quantify ~all:true env e.expr_effect f

and wp_recfun env (_, bl, _var, t) =
  let f = wp_triple env t in
  wp_binders bl f

let wp env e = 
  wp_expr env e (default_post e.expr_type e.expr_effect)

let add_wp_decl l f env =
  let pr = create_prsymbol (id_fresh ("WP_" ^ l.ls_name.id_string)) in
  let d = create_prop_decl Pgoal pr f in
  add_decl d env

let decl env = function
  | Pgm_ttree.Dlet (ls, e) ->
      if !debug then
	eprintf "@[--effect %a-----@\n  %a@]@\n----------------@."
	  Pretty.print_ls ls print_type_v e.expr_type_v;
      let f = wp env e in
      if !debug then
	eprintf "wp = %a@\n----------------@." Pretty.print_fmla f;
      let env = add_wp_decl ls f env in	
      env
  | Pgm_ttree.Dletrec dl ->
      let add_one env (ls, def) = 
	let f = wp_recfun env def in 
	if !debug then
	  eprintf "wp %a = %a@\n----------------@." 
	    print_ls ls Pretty.print_fmla f;
	add_wp_decl ls f env
      in
      List.fold_left add_one env dl
  | Pgm_ttree.Dparam _ ->
      env

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
