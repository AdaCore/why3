(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Why3
open Ident
open Ty
open Term
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** WP-only builtins *)

let ts_mark = create_tysymbol (id_fresh "'mark") [] None
let ty_mark = ty_app ts_mark []

let fs_at =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "at") [ty; ty_mark] (Some ty)

let fs_old =
  let ty = ty_var (create_tvsymbol (id_fresh "a")) in
  create_lsymbol (id_fresh "old") [ty] (Some ty)

let th_mark =
  let uc = create_theory (id_fresh "WP builtins") in
  let uc = add_ty_decl uc ts_mark in
  let uc = add_param_decl uc fs_at in
  let uc = add_param_decl uc fs_old in
  close_theory uc

let fs_setmark =
  create_lsymbol (id_fresh "set_mark") [] (Some ty_mark)

let e_setmark = e_lapp fs_setmark [] (ity_pur ts_mark [])

let vs_old = create_vsymbol (id_fresh "'old") ty_mark
let vs_now = create_vsymbol (id_fresh "'now") ty_mark

(** Weakest preconditions *)

let ty_of_vty = function
  | VTvalue vtv -> ty_of_ity vtv.vtv_ity
  | VTarrow _   -> ty_unit

let default_exn_post xs _ =
  let vs = create_vsymbol (id_fresh "result") (ty_of_ity xs.xs_ity) in
  create_post vs t_true

let default_post vty ef =
  let vs = create_vsymbol (id_fresh "result") (ty_of_vty vty) in
  create_post vs t_true,
  Mexn.mapi default_exn_post ef.eff_raises

let rec wp_expr _km _lkm _e _q =
  assert false (*TODO*)

let wp_close _km _lkm _ef _f =
  assert false (*TODO*)

let wp km lkm e =
  let f = wp_expr km lkm e (default_post e.e_vty e.e_effect) in
  wp_close km lkm e.e_effect f

let wp_val _km th _lv =
  th

let wp_let _km th _ld =
  th

let wp_rec _km th _rdl =
  th

