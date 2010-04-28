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

let rec elim_t func pred map t = match t.t_node with
  | Tvar vs ->
      (try Mvs.find vs map with Not_found -> t)
  | Tlet (t1,tb) when func ->
      let vs,t2 = t_open_bound tb in
      let t1 = elim_t func pred map t1 in
      elim_t func pred (Mvs.add vs t1 map) t2
  | _ ->
      t_map (elim_t func pred map) (elim_f func pred map) t

and elim_f func pred map f = match f.f_node with
  | Flet (t1,fb) when pred ->
      let vs,f2 = f_open_bound fb in
      let t1 = elim_t func pred map t1 in
      elim_f func pred (Mvs.add vs t1 map) f2
  | _ ->
      f_map (elim_t func pred map) (elim_f func pred map) f

let eliminate_let_term = Register.store (fun () -> Trans.rewrite
  (elim_t true false Mvs.empty) (elim_f true false Mvs.empty) None)

let eliminate_let_fmla = Register.store (fun () -> Trans.rewrite
  (elim_t false true Mvs.empty) (elim_f false true Mvs.empty) None)

let eliminate_let = Register.store (fun () -> Trans.rewrite
  (elim_t true true Mvs.empty) (elim_f true true Mvs.empty) None)

let () =
  Register.register_transform "eliminate_let_term" eliminate_let_term;
  Register.register_transform "eliminate_let_fmla" eliminate_let_fmla;
  Register.register_transform "eliminate_let" eliminate_let

