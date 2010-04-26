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
  mt_map : lsymbol Mts.t;       (* from type symbols to selector functions *)
  pj_map : lsymbol list Mls.t;  (* from constructors to projections *)
}

let empty_state = {
  mt_map = Mts.empty;
  pj_map = Mls.empty;
}

let uncompiled = "eliminate_algebraic: compile_match required"

let rec rewriteT kn state t = match t.t_node with
  | Tcase ([t1],bl) ->
      let t1 = rewriteT kn state t1 in
      let mk_br (w,m) br =
        let (pl,e) = t_open_branch br in
        let e = rewriteT kn state e in
        match pl with
        | [{ pat_node = Papp (cs,pl) }] ->
            let add_var e p pj = match p.pat_node with
              | Pvar v -> t_let v (t_app pj [t1] v.vs_ty) e
              | _ -> Register.unsupportedExpression (Term t) uncompiled
            in
            let pjl = Mls.find cs state.pj_map in
            let e = List.fold_left2 add_var e pl pjl in
            w, Mls.add cs e m
        | [{ pat_node = Pwild }] ->
            Some e, m
        | _ -> Register.unsupportedExpression (Term t) uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs = try Mls.find cs m with Not_found -> of_option w in
      let ts = match t1.t_ty.ty_node with
        | Tyapp (ts,_) -> ts
        | _ -> Register.unsupportedExpression (Term t) uncompiled
      in
      let tl = List.map find (find_constructors kn ts) in
      t_app (Mts.find ts state.mt_map) (t1::tl) t.t_ty
  | Tcase _ -> Register.unsupportedExpression (Term t) uncompiled
  | _ -> t_map (rewriteT kn state) (rewriteF kn state true) t

and rewriteF kn state sign f = match f.f_node with
  | Fcase ([t1],bl) ->
      let t1 = rewriteT kn state t1 in
      let mk_br (w,m) br =
        let (pl,e) = f_open_branch br in
        let e = rewriteF kn state sign e in
        match pl with
        | [{ pat_node = Papp (cs,pl) }] ->
            let get_var p = match p.pat_node with
              | Pvar v -> v
              | _ -> Register.unsupportedExpression (Fmla f) uncompiled
            in
            w, Mls.add cs (List.map get_var pl, e) m
        | [{ pat_node = Pwild }] ->
            Some e, m
        | _ -> Register.unsupportedExpression (Fmla f) uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs =
        let vl,e = try Mls.find cs m with Not_found ->
          let var = create_vsymbol (id_fresh "w") in
          let get_var pj = var (t_app_infer pj [t1]).t_ty in
          List.map get_var (Mls.find cs state.pj_map), of_option w
        in
        let hd = t_app cs (List.map t_var vl) t1.t_ty in
        let tr = [] (* FIXME? [[Term hd]] *) in
        let hd = f_equ t1 hd in
        if sign
          then f_forall_simp vl tr (f_implies_simp hd e)
          else f_exists_simp vl tr (f_and_simp     hd e)
      in
      let ts = match t1.t_ty.ty_node with
        | Tyapp (ts,_) -> ts
        | _ -> Register.unsupportedExpression (Fmla f) uncompiled
      in
      let op = if sign then f_and_simp else f_or_simp in
      map_join_left find op (find_constructors kn ts)
  | Fcase _ -> Register.unsupportedExpression (Fmla f) uncompiled
  | _ -> f_map_sign (rewriteT kn state) (rewriteF kn state) sign f

let add_type (state, task) ts csl =
  (* declare constructors as abstract functions *)
  let cs_add tsk cs = add_decl tsk (create_logic_decl [cs, None]) in
  let task = List.fold_left cs_add task csl in
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
    let id = mt_ls.ls_name.id_long ^ "_" ^ cs.ls_name.id_long in
    let pr = create_prsymbol (id_derive id cs.ls_name) in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let hd = t_app cs (List.rev_map t_var vl) (of_option cs.ls_value) in
    let hd = t_app mt_ls (hd::mt_tl) mt_ty in
    let vl = List.rev_append mt_vl (List.rev vl) in
    let ax = f_forall vl [[Term hd]] (f_equ hd t) in
    add_decl tsk (create_prop_decl Paxiom pr ax)
  in
  let task = List.fold_left2 mt_add task csl mt_tl in
  (* declare and define the projection functions *)
  let pj_add (m,tsk) cs =
    let id = cs.ls_name.id_long ^ "_proj_" in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let tl = List.rev_map t_var vl in
    let hd = t_app cs tl (of_option cs.ls_value) in
    let c = ref 0 in
    let add (pjl,tsk) t =
      let id = id_derive (id ^ (incr c; string_of_int !c)) cs.ls_name in
      let ls = create_fsymbol id [of_option cs.ls_value] t.t_ty in
      let tsk = add_decl tsk (create_logic_decl [ls, None]) in
      let id = id_derive (ls.ls_name.id_long ^ "_def") ls.ls_name in
      let pr = create_prsymbol id in
      let hh = t_app ls [hd] t.t_ty in
      let ax = f_forall (List.rev vl) [[Term hd]] (f_equ hh t) in
      ls::pjl, add_decl tsk (create_prop_decl Paxiom pr ax)
    in
    let pjl,tsk = List.fold_left add ([],tsk) tl in
    Mls.add cs (List.rev pjl) m, tsk
  in
  let pjmap, task = List.fold_left pj_add (state.pj_map, task) csl in
  (* add the inversion axiom *)
  let ax_id = ts.ts_name.id_long ^ "_inversion" in
  let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in
  let ax_vs = create_vsymbol (id_fresh "u") mt_hd in
  let ax_hd = t_var ax_vs in
  let mk_cs cs =
    let pjl = Mls.find cs pjmap in
    let app pj = t_app_infer pj [ax_hd] in
    f_equ ax_hd (t_app cs (List.map app pjl) mt_hd)
  in
  let ax_f = f_forall [ax_vs] [] (map_join_left mk_cs f_or csl) in
  let task = add_decl task (create_prop_decl Paxiom ax_pr ax_f) in
  (* return the updated state and task *)
  { mt_map = mtmap; pj_map = pjmap }, task

let comp t (state,task) = match t.task_decl with
  | Decl { d_node = Dtype dl } ->
      (* add abstract type declarations *)
      let tydl = List.rev_map (fun (ts,_) -> (ts,Tabstract)) dl in
      let task = add_decl task (create_ty_decl tydl) in
      (* add needed functions and axioms *)
      let add acc (ts,df) = match df with
        | Tabstract      -> acc
        | Talgebraic csl -> add_type acc ts csl
      in
      List.fold_left add (state,task) dl
  | Decl d ->
      let fnT = rewriteT t.task_known state in
      let fnF = rewriteF t.task_known state true in
      state, add_decl task (decl_map fnT fnF d)
  | td ->
      state, add_tdecl task td

let comp = Register.store (fun () -> Trans.fold_map comp empty_state None)

let () = Register.register_transform "eliminate_algebraic" comp

