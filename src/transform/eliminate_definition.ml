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
open Term
open Decl

(** Discard definitions of built-in symbols *)

let add_ld q = function
  | ls, Some _ when Sid.mem ls.ls_name q -> (ls, None)
  | d -> d

let add_id q (ld,id) = function
  | ls, _ when Sid.mem ls.ls_name q -> (ls, None)::ld, id
  | d -> ld, d::id

let elim q d = match d.d_node with
  | Dlogic l ->
      create_logic_decls (List.map (add_ld q) l)
  | Dind l ->
      let ld, id = List.fold_left (add_id q) ([],[]) l in
      create_logic_decls (List.rev ld) @ create_ind_decls (List.rev id)
  | _ -> [d]

let eliminate_builtin =
  Trans.on_metas
    [ Printer.meta_remove_type;
      Printer.meta_remove_logic;
      Printer.meta_remove_prop ]
    (fun mm ->
      Trans.decl (elim (Mstr.fold Task.find_tagged mm Sid.empty)) None)

let () = Trans.register_transform "eliminate_builtin" eliminate_builtin

(** Eliminate definitions of functions and predicates *)

let rec t_insert hd t = match t.t_node with
  | Tif (f1,t2,t3) ->
      f_if f1 (t_insert hd t2) (t_insert hd t3)
  | Tlet (t1,bt) ->
      let v,t2 = t_open_bound bt in
      f_let v t1 (t_insert hd t2)
  | Tcase (tl,bl) ->
      let br b = let pl,t1 = t_open_branch b in pl, t_insert hd t1 in
      f_case tl (List.map br bl)
  | _ -> f_equ_simp hd t

let rec f_insert hd f = match f.f_node with
  | Fif (f1,f2,f3) ->
      f_if f1 (f_insert hd f2) (f_insert hd f3)
  | Flet (t1,bf) ->
      let v,f2 = f_open_bound bf in
      f_let v t1 (f_insert hd f2)
  | Fcase (tl,bl) ->
      let br b = let pl,f1 = f_open_branch b in pl, f_insert hd f1 in
      f_case tl (List.map br bl)
  | _ -> f_iff_simp hd f

let add_ld func pred axl d = match d with
  | _, None ->
      axl, d
  | ls, Some ld ->
      let vl,e = open_ls_defn ld in begin match e with
        | Term t when func ->
            let nm = ls.ls_name.id_string ^ "_def" in
            let hd = t_app ls (List.map t_var vl) t.t_ty in
            let ax = f_forall vl [[Term hd]] (t_insert hd t) in
            let pr = create_prsymbol (id_derive nm ls.ls_name) in
            create_prop_decl Paxiom pr ax :: axl, (ls, None)
        | Fmla f when pred ->
            let nm = ls.ls_name.id_string ^ "_def" in
            let hd = f_app ls (List.map t_var vl) in
            let ax = f_forall vl [[Fmla hd]] (f_insert hd f) in
            let pr = create_prsymbol (id_derive nm ls.ls_name) in
            create_prop_decl Paxiom pr ax :: axl, (ls, None)
        | _ -> axl, d
      end

let elim func pred mutual d = match d.d_node with
  | Dlogic l when not mutual || List.length l > 1 ->
      let axl, l = map_fold_left (add_ld func pred) [] l in
      let d = create_logic_decl l in
      d :: List.rev axl
  | _ -> [d]

let eliminate_definition_func  = Trans.decl (elim true false false) None
let eliminate_definition_pred  = Trans.decl (elim false true false) None
let eliminate_definition       = Trans.decl (elim true true false) None
let eliminate_mutual_recursion = Trans.decl (elim true true true) None

let () =
  Trans.register_transform "eliminate_definition_func"
    eliminate_definition_func;
  Trans.register_transform "eliminate_definition_pred"
    eliminate_definition_pred;
  Trans.register_transform "eliminate_definition"
    eliminate_definition;
  Trans.register_transform "eliminate_mutual_recursion"
    eliminate_mutual_recursion


