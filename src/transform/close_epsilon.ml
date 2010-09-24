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
open Theory
open Decl
open Task
open Term

let forall_merge vs f =
  match f.f_node with
  | Fquant (Fforall, fq) ->
      let vs', trs, f = f_open_quant fq in
      f_forall_close (vs@vs') trs f
  | _ -> f_forall_close vs [] f

let rec rewriteT t = match t.t_node with
  | Teps fb ->
      let fv = Svs.elements (t_freevars Svs.empty t) in
      let x, f = f_open_bound fb in
      let f = rewriteF f in
      if fv = [] then t_eps_close x f
      else
        (* the type, symbol and term of the new epsilon-symbol [magic] *)
        let magic_ty =
          List.fold_right (fun x acc -> Ty.ty_func x.vs_ty acc) fv x.vs_ty in
        let magic_fs = create_vsymbol (Ident.id_fresh "f") magic_ty in
        let magic_f = t_var magic_fs in
        (* the application of [magic] to the free variables *)
        let rx =
          List.fold_left (fun acc x -> t_func_app acc (t_var x)) magic_f fv in
        (* substitute [magic] for [x] *)
        let f = f_subst_single x rx f in
        (* quantify over free variables and epsilon-close over [magic] *)
        let f = forall_merge fv f in
        let f = t_eps_close magic_fs f in
        (* apply epsilon-term to variables *)
        List.fold_left (fun acc x -> t_func_app acc (t_var x)) f fv
  | _ ->
      t_map rewriteT rewriteF t

and rewriteF f = f_map rewriteT rewriteF f

let comp t task =
  match t.task_decl.td_node with
  | Decl d -> add_decl task (decl_map rewriteT rewriteF d)
  | _ -> add_tdecl task t.task_decl

let close_epsilon =
  Trans.fold comp None

let () = Trans.register_transform "close_epsilon" close_epsilon
