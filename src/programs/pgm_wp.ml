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
open Pgm_ttree
open Pgm_itree
open Pgm_typing

module E = Pgm_effect

type env = {
  uc      : theory_uc;
  globals : type_v Mls.t;
  locals  : type_v Mvs.t;
}

let empty_env uc = { uc = uc; globals = Mls.empty; locals = Mvs.empty }
let add_local x v env = { env with locals = Mvs.add x v env.locals }
let add_global x v env = { env with globals = Mls.add x v env.globals }

let ts_ref   env = ns_find_ts (get_namespace env.uc) ["ref"]
let ts_label env = ns_find_ts (get_namespace env.uc) ["label"]

let ls_old  env = ns_find_ls (get_namespace env.uc) ["old"]
let ls_at   env = ns_find_ls (get_namespace env.uc) ["at"]
let ls_bang env = ns_find_ls (get_namespace env.uc) ["prefix !"]

(* phase 3: translation to intermediate trees and effect inference **********)

let reference_of_term t = match t.t_node with
  | Tvar vs -> E.Rlocal vs
  | Tapp (ls, []) -> E.Rglobal ls
  | _ -> assert false

let rec term_effect env ef t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls (ls_bang env) ->
      let r = reference_of_term t in
      E.add_read r ef
  | _ ->
      t_fold (term_effect env) (fmla_effect env) ef t

and fmla_effect env ef f =
  f_fold (term_effect env) (fmla_effect env) ef f

let post_effect env ef ((_,q),ql) =
  let exn_effect ef (_,(_,q)) = fmla_effect env ef q in
  List.fold_left exn_effect (fmla_effect env ef q) ql

let add_binder env (x, v) = add_local x v env
let add_binders = List.fold_left add_binder

let rec expr env e =
  let ty = e.Pgm_ttree.expr_type in
  let loc = e.Pgm_ttree.expr_loc in
  let d, v, ef = expr_desc env loc ty e.Pgm_ttree.expr_desc in
  { expr_desc = d; expr_type = ty; 
    expr_type_v = v; expr_effect = ef; expr_loc = loc }

and expr_desc env _loc ty = function
  | Pgm_ttree.Elogic t ->
      let ef = term_effect env E.empty t in
      Elogic t, Tpure ty, ef
  | Pgm_ttree.Elocal vs ->
      assert (Mvs.mem vs env.locals);
      Elocal vs, Mvs.find vs env.locals, E.empty
  | Pgm_ttree.Eglobal ls ->
      assert (Mls.mem ls env.globals);
      Eglobal ls, Mls.find ls env.globals, E.empty
  | Pgm_ttree.Eapply _ ->
      assert false (*TODO*)
  | Pgm_ttree.Eapply_ref _ ->
      assert false (*TODO*)
  | Pgm_ttree.Efun (bl, t) ->
      let env = add_binders env bl in
      let t, c = triple env t in
      Efun (bl, t), Tarrow (bl, c), E.empty
  | Pgm_ttree.Elet (v, e1, e2) ->
      let e1 = expr env e1 in
      let env = { env with locals = Mvs.add v e1.expr_type_v env.locals } in
      let e2 = expr env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      Elet (v, e1, e2), e2.expr_type_v, ef

  | Pgm_ttree.Esequence (e1, e2) ->
      let e1 = expr env e1 in
      let e2 = expr env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      Esequence (e1, e2), e2.expr_type_v, ef

  | Pgm_ttree.Eassert (k, f) ->
      let ef = fmla_effect env E.empty f in
      Eassert (k, f), Tpure ty, ef
  | Pgm_ttree.Elabel (lab, e1) ->
      let e1 = expr env e1 in
      Elabel (lab, e1), e1.expr_type_v, e1.expr_effect

  | _ -> 
      assert false (*TODO*)

and triple env (p, e, q) =
  let e = expr env e in
  let ef = post_effect env (fmla_effect env e.expr_effect p) q in
  let e = { e with expr_effect = ef } in
  let c = 
    { c_result_type = e.expr_type_v;
      c_effect      = ef;
      c_pre         = p;
      c_post        = q }
  in
  (p, e, q), c

and recfun _env _def =
  assert false (*TODO*)

(* phase 4: weakest preconditions *******************************************)

(* TODO: use simp forms / tag with label "WP" *)
let wp_and     = f_and
let wp_implies = f_implies
let wp_forall  = f_forall

let fresh_label env =
  let ty = ty_app (ts_label env) [] in
  create_vsymbol (id_fresh "label") ty

let wp_binder (x, tv) f = match tv with
  | Tpure _ -> wp_forall [x] [] f
  | Tarrow _ -> f

let wp_binders = List.fold_right wp_binder 

let post_map f ((v, q), ql) = 
  (v, f q), List.map (fun (e,(v,q)) -> e, (v, f q)) ql

(* replace old(t) with at(t,lab) everywhere in formula f *)
let rec old_label env lab f =
  f_map (old_label_term env lab) (old_label env lab) f

and old_label_term env lab t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls (ls_old env) ->
      let t = old_label_term env lab t in (* NECESSARY? *)
      t_app (ls_at env) [t; t_var lab] t.t_ty
  | _ ->
      t_map (old_label_term env lab) (old_label env lab) t

(* replace at(t,lab) with t everywhere in formula f *)
let rec erase_label env lab f =
  f_map (erase_label_term env lab) (erase_label env lab) f

and erase_label_term env lab t = match t.t_node with
  | Tapp (ls, [t; {t_node = Tvar l}]) 
    when ls_equal ls (ls_at env) && vs_equal l lab ->
      erase_label_term env lab t
  | _ ->
      t_map (erase_label_term env lab) (erase_label env lab) t

let unref_ty env ty = match ty.ty_node with
  | Tyapp (ts, [ty]) when ts_equal ts (ts_ref env) -> ty
  | _ -> assert false

(* replace !r by v everywhere in formula f *)
let rec unref env r v f =
  f_map (unref_term env r v) (unref env r v) f

and unref_term env r v t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls (ls_bang env) ->
      let rt = reference_of_term t in
      if E.ref_equal rt r then t_var v else t
  | Tapp (ls, _) when ls_equal ls (ls_old env) ->
      assert false
  | Tapp (ls, _) when ls_equal ls (ls_at env) -> (* do not recurse in at(...) *)
      t 
  | _ ->
      t_map (unref_term env r v) (unref env r v) t

(* quantify over all references in ef *)
let quantify env ef f =
  let quantify1 r f = 
    let ty = unref_ty env (E.type_of_reference r) in
    let v = create_vsymbol (id_clone (E.name_of_reference r)) ty in
    wp_forall [v] [] (unref env r v f)
  in
  let s = E.Sref.union ef.E.reads ef.E.writes in
  E.Sref.fold quantify1 s f

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in effect [ef] *)

let filter_post ef (q, ql) =
  let keep (ls, _) = Sls.mem ls ef.E.raises in
  q, List.filter keep ql

let rec ls_assoc ls = function
  | [] -> raise Not_found
  | (ls', x) :: _ when ls_equal ls ls' -> x
  | _ :: r -> ls_assoc ls r

let v_result ty = create_vsymbol (id_fresh "result") ty

let exn_v_result ls = match ls.ls_args with
  | [] -> None
  | [ty] -> Some (v_result ty)
  | _ -> assert false

let default_exn_post ls = ls, (exn_v_result ls, f_true)

let default_post ty ef =
  (v_result ty, f_true), 
  List.map default_exn_post (Sls.elements ef.E.raises)

(*s [saturate_post ef f q] makes a postcondition for a program of effect [ef]
    out of a normal postcondition [f] and the exc. postconditions from [q] *)

let saturate_post ty ef f (_, ql) = 
  let set_post x = try x, ls_assoc x ql with Not_found -> default_exn_post x in
  let xs = Sls.elements ef.E.raises in
  ((v_result ty, f), List.map set_post xs)

let rec wp_expr env e q = 
  let lab = fresh_label env in
  let q = post_map (old_label env lab) q in
  let f = wp_desc env e q in
  let f = erase_label env lab f in
  f

and wp_desc env e q = match e.expr_desc with
  | Elogic t ->
      let (v, q), _ = q in
      f_let v t q
  | Efun (bl, t) ->
      let (_, q), _ = q in
      let f = wp_triple env t in
      wp_and q (wp_binders bl f)

  | Esequence (e1, e2) ->
      let w2 = wp_expr env e2 (filter_post e2.expr_effect q) in
      let q1 = saturate_post e1.expr_type e1.expr_effect w2 q in
      wp_expr env e1 q1

  | Eassert (Pgm_ptree.Aassert, f) ->
      let (_, q), _ = q in
      wp_and f q
  | Eassert (Pgm_ptree.Acheck, f) ->
      let (_, q), _ = q in
      f_and f q (* symetric conjunction instead *)
  | Eassert (Pgm_ptree.Aassume, f) ->
      let (_, q), _ = q in
      wp_implies f q
  | Elabel (lab, e1) ->
      let w1 = wp_expr env e1 q in
      erase_label env lab w1

  | _ -> 
      f_true (* TODO *)

and wp_triple env (p, e, q) =
  let f = wp_expr env e q in
  let f = wp_implies p f in
  quantify env e.expr_effect f

let wp env e = 
  wp_expr env e (default_post e.expr_type e.expr_effect)

let wp_recfun _env _l _def = f_true (* TODO *)

let add_wp_decl l f env =
  let pr = create_prsymbol (id_fresh ("WP_" ^ l.ls_name.id_string)) in
  let d = create_prop_decl Pgoal pr f in
  { env with uc = add_decl env.uc d }

let decl env = function
  | Pgm_ttree.Dlet (ls, e) ->
      let e = expr env e in
      (* DEBUG *)
      eprintf "@[--effect %a-----@\n  %a@]@\n----------------@." 
	Pretty.print_ls ls print_type_v e.expr_type_v;
      let f = wp env e in
      eprintf "wp = %a@\n----------------@." Pretty.print_fmla f;
      let env = add_wp_decl ls f env in
      let env = add_global ls e.expr_type_v env in
      env
  | Pgm_ttree.Dletrec dl ->
      let add_one env (ls, def) = 
	let def = recfun env def in
	let f = wp_recfun env ls def in 
	let env = add_wp_decl ls f env in
	let v = assert false (*TODO*) in
	let env = add_global ls v env in
	env
      in
      List.fold_left add_one env dl
  | Pgm_ttree.Dparam (ls, v) ->
      let env = add_global ls v env in
      env

let file uc dl =
  let env = List.fold_left decl (empty_env uc) dl in
  Theory.close_theory env.uc

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
