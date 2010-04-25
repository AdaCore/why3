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

(* eliminate if-then-else in terms *)

let rec remove_if_t letl contT t = match t.t_node with
  | Tlet (t1,tb) ->
      let u,t2 = t_open_bound tb in
      let t_let e1 e2 =
        if e1 == t1 && e2 == t2 then t else t_let u e1 e2
      in
      let cont_in t1 t2 = contT (t_let t1 t2) in
      let cont_let t1 = remove_if_t ((u,t1)::letl) (cont_in t1) t2 in
      remove_if_t letl cont_let t1
  | Tif (f,t1,t2) ->
      let f = remove_if_f (fun f -> f) f in
      let f = List.fold_left (fun f (v,t) -> f_let v t f) f letl in
      f_if f (remove_if_t letl contT t1) (remove_if_t letl contT t2)
  | _ ->
      t_map_cont (remove_if_t letl) remove_if_f contT t

and remove_if_f contF f = match f.f_node with
  | Fapp _ | Flet _ | Fcase _ ->
      contF (f_map_cont (remove_if_t []) remove_if_f (fun f -> f) f)
  | _ ->
      f_map_cont (fun _ _ -> assert false) remove_if_f contF f

let remove_if_f f = remove_if_f (fun f -> f) f

let add_ld axl d = match d with
  | _, None -> axl, d
  | ls, Some ld ->
      let vl,e = open_ls_defn ld in
      begin match e with
        | Term _ ->
            let f = ls_defn_axiom ld in
            let g = remove_if_f f in
            if f == g then axl, d
(*          else if Driver.query_remove q ls.ls_name then axl, (ls, None) *)
            else
              let nm = ls.ls_name.id_short ^ "_def" in
              let pr = create_prsymbol (id_derive nm ls.ls_name) in
              create_prop_decl Paxiom pr g :: axl, (ls, None)
        | Fmla f ->
            axl, make_ps_defn ls vl (remove_if_f f)
      end

let remove_if_decl d = match d.d_node with
  | Dlogic l ->
      let axl, l = map_fold_left add_ld [] l in
      let d = create_logic_decl l in
      d :: List.rev axl
  | _ ->
      [decl_map (fun _ -> assert false) remove_if_f d]

let eliminate_if_term =
  Register.store (fun () -> Trans.decl remove_if_decl None)

let () = Register.register_transform "eliminate_if_term" eliminate_if_term

(* eliminate if-then-else in formulas *)

let rec remove_if_t t = t_map remove_if_t (remove_if_f true) t

and remove_if_f sign f = match f.f_node with
  | Fif (f1,f2,f3) ->
      let f1p = remove_if_f sign f1 in
      let f1n = remove_if_f (not sign) f1 in
      let f2 = remove_if_f sign f2 in
      let f3 = remove_if_f sign f3 in
      if sign then f_and (f_implies f1n f2) (f_or f1p f3)
              else f_or (f_and f1p f2) (f_and (f_not f1n) f3)
  | _ ->
      f_map_sign remove_if_t remove_if_f sign f

let eliminate_if_fmla =
  Register.store (fun () -> Trans.rewrite remove_if_t (remove_if_f true) None)

let () = Register.register_transform "eliminate_if_fmla" eliminate_if_fmla

