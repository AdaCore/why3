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

open Util
open Ident
open Ty
open Term
open Decl
open Task

type state = {
  cs_map : lsymbol Mls.t;       (* from constructors to abstract functions *)
  mt_map : lsymbol Mts.t;       (* from type symbols to selector functions *)
  pj_map : lsymbol list Mls.t;  (* from constructors to projections *)
}

let empty_state = {
  cs_map = Mls.empty;
  mt_map = Mts.empty;
  pj_map = Mls.empty;
}

let rec rewriteT state t = match t.t_node with
  | Tcase (tl,bl) -> assert false
(*
      let mk_b (pl,_,t) = (pl,t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      Pattern.CompileTerm.compile (find_constructors state) tl bl
*)
  | _ -> t_map (rewriteT state) (rewriteF state) t

and rewriteF state f = match f.f_node with
  | Fcase (tl,bl) -> assert false
(*
      let mk_b (pl,_,f) = (pl,f) in
      let bl = List.map (fun b -> mk_b (f_open_branch b)) bl in
      Pattern.CompileFmla.compile (find_constructors state) tl bl
*)
  | _ -> f_map (rewriteT state) (rewriteF state) f

let add_type (state, task) ts csl =
  (* declare constructors as abstract functions *)
  let cs_add (m,tsk) cs =
    let id = id_clone cs.ls_name in
    let fs = create_fsymbol id cs.ls_args (of_option cs.ls_value) in
    Mls.add cs fs m, add_decl tsk (create_logic_decl [fs, None])
  in
  let csmap, task = List.fold_left cs_add (state.cs_map, task) csl in
  (* declare the selector function *)
  let mt_id = id_derive ("match_" ^ ts.ts_name.id_long) ts.ts_name in
  let mt_hd = ty_app ts (List.map ty_var ts.ts_args) in
  let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in
  let mt_al = mt_hd :: List.rev_map (fun _ -> mt_ty) csl in
  let mt_ls = create_fsymbol mt_id mt_al mt_ty in
  let mtmap = Mts.add ts mt_ls state.mt_map in
  let task  = add_decl task (create_logic_decl [mt_ls, None]) in
  (* define the selector function *)
  let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in
  let mt_vl = List.rev_map mt_vs csl in
  let mt_tl = List.rev_map t_var mt_vl in
  let mt_add tsk cs t =
    let fs = Mls.find cs csmap in
    let id = mt_ls.ls_name.id_long ^ "_" ^ cs.ls_name.id_long in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) fs.ls_args in
    let hd = t_app fs (List.rev_map t_var vl) (of_option fs.ls_value) in
    let hd = t_app mt_ls (hd::mt_tl) mt_ty in
    let vl = List.rev_append mt_vl (List.rev vl) in
    let ax = f_forall vl [[Term hd]] (f_equ hd t) in
    add_decl tsk (create_prop_decl Paxiom pr ax)
  in
  let task = List.fold_left2 mt_add task csl mt_tl in
  (* declare and define the projection functions *)
  let pj_add (m,tsk) cs =
    let fs = Mls.find cs csmap in
    let id = cs.ls_name.id_long ^ "_proj_" in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) fs.ls_args in
    let tl = List.rev_map t_var vl in
    let hd = t_app fs tl (of_option fs.ls_value) in
    let c = ref 0 in
    let add (pjl,tsk) t =
      let id = id_derive (id ^ (incr c; string_of_int !c)) cs.ls_name in
      let ls = create_fsymbol id [of_option fs.ls_value] t.t_ty in
      let tsk = add_decl tsk (create_logic_decl [ls, None]) in
      let id = id_derive (ls.ls_name.id_long ^ "_def") ls.ls_name in
      let pr = create_prsymbol id in
      let hh = t_app ls [hd] t.t_ty in
      let ax = f_forall (List.rev vl) [[Term hd]] (f_equ hh t) in
      ls::pjl, add_decl tsk (create_prop_decl Paxiom pr ax)
    in
    let pjl,tsk = List.fold_left add ([],tsk) tl in
    Mls.add cs pjl m, tsk
  in
  let pjmap, task = List.fold_left pj_add (state.pj_map, task) csl in
  (* add the inversion axiom *)
  let ax_id = ts.ts_name.id_long ^ "_inversion" in
  let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in
  let ax_vs = create_vsymbol (id_fresh "u") mt_hd in
  let ax_hd = t_var ax_vs in
  let mk_cs cs =
    let fs  = Mls.find cs csmap in
    let pjl = Mls.find cs pjmap in
    let app pj = t_app_infer pj [ax_hd] in
    f_equ ax_hd (t_app fs (List.rev_map app pjl) mt_hd)
  in
  let ax_f = f_forall [ax_vs] [] (map_join_left mk_cs f_or csl) in
  let task = add_decl task (create_prop_decl Paxiom ax_pr ax_f) in
  (* return the updated state and task *)
  { cs_map = csmap; mt_map = mtmap; pj_map = pjmap }, task

let comp t (state,task) = match t.task_decl.d_node with
  | Dtype dl ->
      (* add abstract type declarations *)
      let tydl = List.rev_map (fun (ts,_) -> (ts,Tabstract)) dl in
      let task = add_decl task (create_ty_decl tydl) in
      (* add needed functions and axioms *)
      let add acc (ts,df) = match df with
        | Tabstract      -> acc
        | Talgebraic csl -> add_type acc ts csl
      in
      List.fold_left add (state,task) dl
  | d ->
      let fnT = rewriteT state in
      let fnF = rewriteF state in
      state, add_decl task (decl_map fnT fnF t.task_decl)

let comp = Register.store (fun () -> Trans.fold_map comp empty_state None)

let () = Driver.register_transform "eliminate_algebraic" comp

