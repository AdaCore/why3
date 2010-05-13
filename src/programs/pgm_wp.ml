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

open Why
open Ident
open Term
open Decl
open Theory
open Pgm_itree

module E = Pgm_effect

let errorm = Pgm_typing.errorm

(* translation to intermediate trees and effect inference *)

let rec expr e =
  let ty = e.Pgm_ttree.expr_type in
  let loc = e.Pgm_ttree.expr_loc in
  let d, ef = expr_desc loc ty e.Pgm_ttree.expr_desc in
  { expr_desc = d; expr_type = ty; expr_effect = ef; expr_loc = loc }

and expr_desc _loc _ty = function
  | Pgm_ttree.Elogic _t ->
      assert false (*TODO*)
  | Pgm_ttree.Eapply _ as _e ->
      assert false (*TODO*)
  | Pgm_ttree.Efun (_bl, (_p, e, _q)) ->
      let _e = expr e in
      assert false (*TODO*)
  | _ -> 
      assert false (*TODO*)

and recfun _ =
  assert false (*TODO*)

(* weakest preconditions *)

let wp _l _e = f_true (* TODO *)

let wp_recfun _l _def = f_true (* TODO *)

let add_wp_decl uc l f =
  let pr = create_prsymbol (id_fresh ("WP_" ^ l.ls_name.id_string)) in
  let d = create_prop_decl Pgoal pr f in
  add_decl uc d

let decl uc = function
  | Pgm_ttree.Dlet (l, e) ->
      let e = expr e in
      let f = wp l e in
      add_wp_decl uc l f
  | Pgm_ttree.Dletrec dl ->
      let add_one uc (l, def) = 
	let def = recfun def in
	let f = wp_recfun l def in 
	add_wp_decl uc l f 
      in
      List.fold_left add_one uc dl
  | Pgm_ttree.Dparam _ ->
      uc

let file uc dl =
  let uc = List.fold_left decl uc dl in
  Theory.close_theory uc
