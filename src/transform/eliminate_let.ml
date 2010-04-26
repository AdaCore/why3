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

(* eliminate let *)

let rec remove_let_t fnF map t = match t.t_node with
  | Tvar vs ->
      (try Mvs.find vs map with Not_found -> t)
  | Tlet (t1,tb) ->
      let t1 = remove_let_t fnF map t1 in
      let vs,t2 = t_open_bound tb in
      remove_let_t fnF (Mvs.add vs t1 map) t2
  | _ ->
      t_map (remove_let_t fnF map) (fnF map) t

and remove_let_f fnT map f = match f.f_node with
  | Flet (t1,fb) ->
      let t1 = fnT map t1 in
      let vs,f2 = f_open_bound fb in
      remove_let_f fnT (Mvs.add vs t1 map) f2
  | _ ->
      f_map (fnT map) (remove_let_f fnT map) f

let rec elim_let_t map t = remove_let_t elim_let_f map t
and     elim_let_f map f = remove_let_f elim_let_t map f

let elim_let_t = elim_let_t Mvs.empty
let elim_let_f = elim_let_f Mvs.empty

let rec skip_t map t = t_map (skip_t map) (remove_let_f skip_t map) t
let rec skip_f map f = f_map (remove_let_t skip_f map) (skip_f map) f

let skip_t = skip_t Mvs.empty
let skip_f = skip_f Mvs.empty

let eliminate_let_term =
  Register.store (fun () -> Trans.rewrite elim_let_t skip_f None)

let eliminate_let_fmla =
  Register.store (fun () -> Trans.rewrite skip_t elim_let_f None)

let eliminate_let =
  Register.store (fun () -> Trans.rewrite elim_let_t elim_let_f None)

let () =
  Register.register_transform "eliminate_let_term" eliminate_let_term;
  Register.register_transform "eliminate_let_fmla" eliminate_let_fmla;
  Register.register_transform "eliminate_let" eliminate_let

