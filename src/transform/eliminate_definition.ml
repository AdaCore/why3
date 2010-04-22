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

let unfold_t lm e = List.fold_left (fun e (v,t) -> t_let v t e) e lm
let unfold_f lm e = List.fold_left (fun e (v,t) -> f_let v t e) e lm

let add_t_ax task nm ls hd e =
  let vl = Svs.elements (t_freevars Svs.empty hd) in
  let ax = f_forall vl [[Term hd]] (f_equ hd e) in
  let id = id_derive (nm ^ "_def") ls.ls_name in
  add_decl task (create_prop_decl Paxiom (create_prsymbol id) ax)

let add_f_ax task nm ls hd e =
  let vl = Svs.elements (f_freevars Svs.empty hd) in
  let ax = f_forall vl [[Fmla hd]] (f_iff_simp hd e) in
  let id = id_derive (nm ^ "_def") ls.ls_name in
  add_decl task (create_prop_decl Paxiom (create_prsymbol id) ax)

let uncompiled = "eliminate_algebraic: compile_match required"

let rec add_fd kn task nm ls hd lm e = match e.t_node with
  | Tlet (t,b) ->
      let v,e = t_open_bound b in
      add_fd kn task nm ls hd ((v,t)::lm) e
  | Tcase ([t],bl) ->
      let t = Eliminate_let.remove_let_t (unfold_t lm t) in
      begin match t.t_node with
        | Tvar v ->
            let mk_br (w,m) br =
              let (pl,e) = t_open_branch br in
              match pl with
              | [{ pat_node = Papp (cs,pl) }] ->
                  let mk_var p = match p.pat_node with
                    | Pvar v -> t_var v
                    | _ -> failwith uncompiled
                  in
                  w, Mls.add cs (t_app cs (List.map mk_var pl) v.vs_ty, e) m
              | [{ pat_node = Pwild }] ->
                  Some e, m
              | _ -> failwith uncompiled
            in
            let w,m = List.fold_left mk_br (None,Mls.empty) bl in
            let find cs = try Mls.find cs m with Not_found ->
              let u = id_fresh "u" in
              let s = ty_match Mtv.empty (of_option cs.ls_value) v.vs_ty in
              let mk_v ty = t_var (create_vsymbol u (ty_inst s ty)) in
              t_app cs (List.map mk_v cs.ls_args) v.vs_ty, of_option w
            in
            let ts = match v.vs_ty.ty_node with
              | Tyapp (ts,_) -> ts
              | _ -> failwith uncompiled
            in
            let add_cs tsk cs =
              let t,e = find cs in
              let lm = lm @ [v,t] in
              let hd = t_subst_single v t hd in
              add_fd kn tsk (nm ^ "_" ^ cs.ls_name.id_long) ls hd lm e
            in
            List.fold_left add_cs task (find_constructors kn ts)
        | _ ->
            add_t_ax task nm ls hd (unfold_t lm e)
      end
  | _ -> add_t_ax task nm ls hd (unfold_t lm e)

let rec add_pd kn task nm ls hd lm e = match e.f_node with
  | Flet (t,b) ->
      let v,e = f_open_bound b in
      add_pd kn task nm ls hd ((v,t)::lm) e
  | Fcase ([t],bl) ->
      let t = Eliminate_let.remove_let_t (unfold_t lm t) in
      begin match t.t_node with
        | Tvar v ->
            let mk_br (w,m) br =
              let (pl,e) = f_open_branch br in
              match pl with
              | [{ pat_node = Papp (cs,pl) }] ->
                  let mk_var p = match p.pat_node with
                    | Pvar v -> t_var v
                    | _ -> failwith uncompiled
                  in
                  w, Mls.add cs (t_app cs (List.map mk_var pl) v.vs_ty, e) m
              | [{ pat_node = Pwild }] ->
                  Some e, m
              | _ -> failwith uncompiled
            in
            let w,m = List.fold_left mk_br (None,Mls.empty) bl in
            let find cs = try Mls.find cs m with Not_found ->
              let u = id_fresh "u" in
              let s = ty_match Mtv.empty (of_option cs.ls_value) v.vs_ty in
              let mk_v ty = t_var (create_vsymbol u (ty_inst s ty)) in
              t_app cs (List.map mk_v cs.ls_args) v.vs_ty, of_option w
            in
            let ts = match v.vs_ty.ty_node with
              | Tyapp (ts,_) -> ts
              | _ -> failwith uncompiled
            in
            let add_cs tsk cs =
              let t,e = find cs in
              let lm = lm @ [v,t] in
              let hd = f_subst_single v t hd in
              add_pd kn tsk (nm ^ "_" ^ cs.ls_name.id_long) ls hd lm e
            in
            List.fold_left add_cs task (find_constructors kn ts)
        | _ ->
            add_f_ax task nm ls hd (unfold_f lm e)
      end
  | _ -> add_f_ax task nm ls hd (unfold_f lm e)

let add_ld kn task ls ld =
  let vl,e = open_ls_defn ld in
  let tl = List.map t_var vl in
  match e with
  | Term t ->
      add_fd kn task ls.ls_name.id_long ls (t_app ls tl t.t_ty) [] t
  | Fmla f ->
      add_pd kn task ls.ls_name.id_long ls (f_app ls tl) [] f

let add_ld kn task (ls,ld) = match ld with
  | None    -> task
  | Some ld -> add_ld kn task ls ld

let add_ls task (ls,_) = add_decl task (create_logic_decl [ls,None])

let elim t task = match t.task_decl with
  | Decl { d_node = Dlogic ll } ->
      let task = List.fold_left add_ls task ll in
      let task = List.fold_left (add_ld t.task_known) task ll in
      task
  | td ->
      add_tdecl task td

let elim = Register.store (fun () -> Trans.map elim None)

let () = Register.register_transform "eliminate_definition" elim

