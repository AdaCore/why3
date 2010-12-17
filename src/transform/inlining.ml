(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

let t_unfold env fs tl ty =
  match Mls.find_option fs env with
  | None ->
      t_app fs tl ty
  | Some (vl, Term e) ->
      let add (mt,mv) x y = ty_match mt x.vs_ty y.t_ty, Mvs.add x y mv in
      let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vl tl in
      let mt = ty_match mt e.t_ty ty in
      t_ty_subst mt mv e
  | _ ->
      assert false

let f_unfold env ps tl =
  match Mls.find_option ps env with
  | None ->
      f_app ps tl
  | Some (vs, Fmla e) ->
      let add (mt,mv) x y = ty_match mt x.vs_ty y.t_ty, Mvs.add x y mv in
      let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vs tl in
      f_ty_subst mt mv e
  | _ ->
      assert false

(* inline every symbol *)

let rec t_replace_all env t =
  let t = t_map (t_replace_all env) (f_replace_all env) t in
  match t.t_node with
  | Tapp (fs,tl) -> t_label_copy t (t_unfold env fs tl t.t_ty)
  | _ -> t

and f_replace_all env f =
  let f = f_map (t_replace_all env) (f_replace_all env) f in
  match f.f_node with
  | Fapp (ps,tl) -> f_label_copy f (f_unfold env ps tl)
  | _ -> f

(* inline the top-most symbol *)

let t_replace_top env t = match t.t_node with
  | Tapp (fs,tl) -> t_label_copy t (t_unfold env fs tl t.t_ty)
  | _ -> t

let rec f_replace_top env f = match f.f_node with
  | Fapp (ps,[l;r]) when ls_equal ps ps_equ ->
      f_label_copy f (f_equ (t_replace_top env l) (t_replace_top env r))
  | Fapp (ps,tl) ->
      f_label_copy f (f_unfold env ps tl)
  | _ ->
      f_map (fun t -> t) (f_replace_top env) f

(* treat a declaration *)

let fold in_goal notdeft notdeff notls d (env, task) =
  let d = match d.d_node with
    | Dprop (Pgoal,_,_) when in_goal ->
        decl_map (fun t -> t) (f_replace_top env) d
    | _ when in_goal ->
        d
    | _ ->
        decl_map (t_replace_all env) (f_replace_all env) d
  in
  match d.d_node with
    | Dlogic [ls,Some ld] when not (notls ls) ->
        let vl,e = open_ls_defn ld in
        let inline = match e with
          | Term t when notdeft t || t_s_any ffalse (ls_equal ls) t -> false
          | Fmla f when notdeff f || f_s_any ffalse (ls_equal ls) f -> false
          | _ -> true
        in
        let env = if inline then Mls.add ls (vl,e) env else env in
        let task = if inline && not in_goal then task else add_decl task d in
        env, task
    | _ ->
        env, add_decl task d

let fold in_goal notdeft notdeff notls task_hd (env, task) =
  match task_hd.task_decl.td_node with
    | Decl d ->
        fold in_goal notdeft notdeff notls d (env, task)
    | _ ->
        env, add_tdecl task task_hd.task_decl

(* transformations *)

let meta = Theory.register_meta "inline : no" [Theory.MTlsymbol]

let t ?(use_meta=true) ?(in_goal=false) ~notdeft ~notdeff ~notls =
  let trans notls =
    Trans.fold_map (fold in_goal notdeft notdeff notls) Mls.empty None in
  if use_meta then
    Trans.on_tagged_ls meta (fun sls ->
      let notls ls = Sls.mem ls sls || notls ls in
      trans notls)
  else
    trans notls

let all = t ~use_meta:true ~in_goal:false
  ~notdeft:ffalse ~notdeff:ffalse ~notls:ffalse

let goal = t ~use_meta:true ~in_goal:true
  ~notdeft:ffalse ~notdeff:ffalse ~notls:ffalse

(* inline_trivial *)

let trivial tl =
  let add vs t = match t.t_node with
    | Tvar v when Mvs.mem v vs -> raise Util.FoldSkip
    | Tvar v -> Svs.add v vs
    | _ when Svs.is_empty (t_freevars Svs.empty t) -> vs
    | _ -> raise Util.FoldSkip
  in
  try ignore (List.fold_left add Svs.empty tl); true
  with Util.FoldSkip -> false

let notdeft t = match t.t_node with
  | Tvar _ | Tconst _ -> false
  | Tapp (_,tl) -> not (trivial tl)
  | _ -> true

let notdeff f = match f.f_node with
  | Ftrue | Ffalse -> false
  | Fapp (_,tl) -> not (trivial tl)
  | _ -> true

let trivial = t ~use_meta:true ~in_goal:false
  ~notdeft:notdeft ~notdeff:notdeff ~notls:ffalse

let () =
  Trans.register_transform "inline_all" all;
  Trans.register_transform "inline_goal" goal;
  Trans.register_transform "inline_trivial" trivial

