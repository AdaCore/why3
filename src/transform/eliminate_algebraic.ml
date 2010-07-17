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
open Theory
open Task

let meta_enum = Theory.register_meta "enumeration" [Theory.MTtysymbol]

(** Compile match patterns *)

let rec rewriteT kn t = match t.t_node with
  | Tcase (t,bl) ->
      let t = rewriteT kn t in
      let mk_b (p,t) = ([p], rewriteT kn t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      Pattern.CompileTerm.compile (find_constructors kn) [t] bl
  | _ -> t_map (rewriteT kn) (rewriteF kn) t

and rewriteF kn f = match f.f_node with
  | Fcase (t,bl) ->
      let t = rewriteT kn t in
      let mk_b (p,f) = ([p], rewriteF kn f) in
      let bl = List.map (fun b -> mk_b (f_open_branch b)) bl in
      Pattern.CompileFmla.compile (find_constructors kn) [t] bl
  | _ -> f_map (rewriteT kn) (rewriteF kn) f

let comp t task =
  let fnT = rewriteT t.task_known in
  let fnF = rewriteF t.task_known in
  match t.task_decl.td_node with
  | Decl d -> add_decl task (decl_map fnT fnF d)
  | _ -> add_tdecl task t.task_decl

let compile_match = Trans.map comp None

(** Eliminate algebraic types and match statements *)

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
  | Tcase (t1,bl) ->
      let t1 = rewriteT kn state t1 in
      let mk_br (w,m) br =
        let (p,e) = t_open_branch br in
        let e = rewriteT kn state e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let add_var e p pj = match p.pat_node with
              | Pvar v -> t_let v (t_app pj [t1] v.vs_ty) e
              | _ -> Printer.unsupportedTerm t uncompiled
            in
            let pjl = Mls.find cs state.pj_map in
            let e = List.fold_left2 add_var e pl pjl in
            w, Mls.add cs e m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs = try Mls.find cs m with Not_found -> of_option w in
      let ts = match t1.t_ty.ty_node with
        | Tyapp (ts,_) -> ts
        | _ -> Printer.unsupportedTerm t uncompiled
      in
      let tl = List.map find (find_constructors kn ts) in
      t_app (Mts.find ts state.mt_map) (t1::tl) t.t_ty
  | _ -> t_map (rewriteT kn state) (rewriteF kn state Svs.empty true) t

and rewriteF kn state av sign f = match f.f_node with
  | Fcase (t1,bl) ->
      let t1 = rewriteT kn state t1 in
      let av' = Svs.diff av (t_freevars Svs.empty t1) in
      let mk_br (w,m) br =
        let (p,e) = f_open_branch br in
        let e = rewriteF kn state av' sign e in
        match p with
        | { pat_node = Papp (cs,pl) } ->
            let get_var p = match p.pat_node with
              | Pvar v -> v
              | _ -> Printer.unsupportedFmla f uncompiled
            in
            w, Mls.add cs (List.map get_var pl, e) m
        | { pat_node = Pwild } ->
            Some e, m
        | _ -> Printer.unsupportedFmla f uncompiled
      in
      let w,m = List.fold_left mk_br (None,Mls.empty) bl in
      let find cs =
        let vl,e = try Mls.find cs m with Not_found ->
          let var = create_vsymbol (id_fresh "w") in
          let get_var pj = var (t_app_infer pj [t1]).t_ty in
          List.map get_var (Mls.find cs state.pj_map), of_option w
        in
        let hd = t_app cs (List.map t_var vl) t1.t_ty in
        match t1.t_node with
        | Tvar v when Svs.mem v av ->
            let hd = f_let v hd e in if sign
            then f_forall_simp vl [] hd
            else f_exists_simp vl [] hd
        | _ ->
            let hd = f_equ t1 hd in if sign
            then f_forall_simp vl [] (f_implies_simp hd e)
            else f_exists_simp vl [] (f_and_simp     hd e)
      in
      let ts = match t1.t_ty.ty_node with
        | Tyapp (ts,_) -> ts
        | _ -> Printer.unsupportedFmla f uncompiled
      in
      let op = if sign then f_and_simp else f_or_simp in
      map_join_left find op (find_constructors kn ts)
  | Fquant (q, bf) when (q = Fforall && sign) || (q = Fexists && not sign) ->
      let vl, tr, f1 = f_open_quant bf in
      let tr' = tr_map (rewriteT kn state)
                       (rewriteF kn state Svs.empty sign) tr in
      let av = List.fold_left (fun s v -> Svs.add v s) av vl in
      let f1' = rewriteF kn state av sign f1 in
      if f_equal f1' f1 && trl_equal tr' tr then f else f_quant q vl tr' f1'
  | Fbinop (o, _, _) when (o = Fand && sign) || (o = For && not sign) ->
      f_map_sign (rewriteT kn state) (rewriteF kn state av) sign f
  | Flet (t1, _) ->
      let av = Svs.diff av (t_freevars Svs.empty t1) in
      f_map_sign (rewriteT kn state) (rewriteF kn state av) sign f
  | _ ->
      f_map_sign (rewriteT kn state) (rewriteF kn state Svs.empty) sign f

let add_type (state, task) ts csl =
  (* declare constructors as abstract functions *)
  let cs_add tsk cs = add_decl tsk (create_logic_decl [cs, None]) in
  let task = List.fold_left cs_add task csl in
  (* declare the selector function *)
  let mt_id = id_derive ("match_" ^ ts.ts_name.id_string) ts.ts_name in
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
    let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in
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
    let id = cs.ls_name.id_string ^ "_proj_" in
    let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in
    let tl = List.rev_map t_var vl in
    let hd = t_app cs tl (of_option cs.ls_value) in
    let c = ref 0 in
    let add (pjl,tsk) t =
      let id = id_derive (id ^ (incr c; string_of_int !c)) cs.ls_name in
      let ls = create_fsymbol id [of_option cs.ls_value] t.t_ty in
      let tsk = add_decl tsk (create_logic_decl [ls, None]) in
      let id = id_derive (ls.ls_name.id_string ^ "_def") ls.ls_name in
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
  let ax_id = ts.ts_name.id_string ^ "_inversion" in
  let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in
  let ax_vs = create_vsymbol (id_fresh "u") mt_hd in
  let ax_hd = t_var ax_vs in
  let mk_cs cs =
    let pjl = Mls.find cs pjmap in
    let app pj = t_app_infer pj [ax_hd] in
    f_equ ax_hd (t_app cs (List.map app pjl) mt_hd)
  in
  let ax_f = map_join_left mk_cs f_or csl in
  let trgl = t_app mt_ls (ax_hd :: mt_tl) mt_ty in
  let ax_f = f_forall (ax_vs :: mt_vl) [[Term trgl]] ax_f in
  let task = add_decl task (create_prop_decl Paxiom ax_pr ax_f) in
  (* add the tag for enumeration if the type is one *)
  let enum = List.for_all (fun ls -> ls.ls_args = []) csl in
  let task = if enum then add_meta task meta_enum [MAts ts] else task in
  (* return the updated state and task *)
  { mt_map = mtmap; pj_map = pjmap }, task

let comp t (state,task) = match t.task_decl.td_node with
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
      let fnF = rewriteF t.task_known state Svs.empty true in
      state, add_decl task (decl_map fnT fnF d)
  | _ ->
      state, add_tdecl task t.task_decl

let eliminate_compiled_algebraic = Trans.fold_map comp empty_state None

let eliminate_algebraic =
  Trans.compose compile_match eliminate_compiled_algebraic

let () = Trans.register_transform "eliminate_algebraic" eliminate_algebraic

