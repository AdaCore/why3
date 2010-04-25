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

let rec t_insert hd t = match t.t_node with
  | Tif (f1,t2,t3) ->
      f_if f1 (t_insert hd t2) (t_insert hd t3)
  | Tlet (t1,bt) ->
      let v,t2 = t_open_bound bt in
      f_let v t1 (t_insert hd t2)
  | Tcase (tl,bl) ->
      let br b = let pl,t1 = t_open_branch b in pl, t_insert hd t1 in
      f_case tl (List.map br bl)
  | _ -> f_equ hd t

let rec f_insert hd f = match f.f_node with
  | Fif (f1,f2,f3) ->
      f_if f1 (f_insert hd f2) (f_insert hd f3)
  | Flet (t1,bf) ->
      let v,f2 = f_open_bound bf in
      f_let v t1 (f_insert hd f2)
  | Fcase (tl,bl) ->
      let br b = let pl,f1 = f_open_branch b in pl, f_insert hd f1 in
      f_case tl (List.map br bl)
  | _ -> f_iff hd f

let add_ld q axl d = match d with
  | _, None -> axl, d
  | ls, _ when Driver.query_remove q ls.ls_name -> axl, (ls, None)
  | ls, Some ld ->
      let nm = ls.ls_name.id_short ^ "_def" in
      let pr = create_prsymbol (id_derive nm ls.ls_name) in
      let vl,e = open_ls_defn ld in
      let tl = List.map t_var vl in
      begin match e with
        | Term t ->
            let hd = t_app ls tl t.t_ty in
            let ax = f_forall vl [[Term hd]] (t_insert hd t) in
            create_prop_decl Paxiom pr ax :: axl, (ls, None)
        | Fmla f ->
            let hd = f_app ls tl in
            let ax = f_forall vl [[Fmla hd]] (f_insert hd f) in
            create_prop_decl Paxiom pr ax :: axl, (ls, None)
      end

let elim q d = match d.d_node with
  | Dlogic l ->
      let axl, l = map_fold_left (add_ld q) [] l in
      let d = create_logic_decl l in
      d :: List.rev axl
  | _ -> [d]

let elim = Register.store_query (fun q -> Trans.decl (elim q) None)

let () = Register.register_transform "eliminate_definition" elim

