(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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
open Util
open Theory
open Env
open Ptree
open Mlw_module

type mlw_contents = modul Mstr.t
type mlw_library = mlw_contents library
type mlw_file = mlw_contents * Theory.theory Mstr.t

    (* let type_only = Debug.test_flag Typing.debug_type_only in *)

let add_theory _lib path mt m =
  let id = m.pth_name in
  let loc = id.id_loc in
  let uc = Theory.create_theory ~path (Denv.create_user_id id) in
  let rec add_decl uc = function
    | Duseclone (_loc, _use, None) (* use *) ->
        assert false (*TODO*)
    | Duseclone (_loc, _use, Some _s) (* clone *) ->
       assert false (*TODO*)
    | Dlogic d ->
        Typing.add_decl uc d
    | Dnamespace (loc, name, import, dl) ->
        let uc = Theory.open_namespace uc in
        let uc = List.fold_left add_decl uc dl in
        Typing.close_namespace loc import name uc
    | Dlet _ | Dletrec _ | Dparam _ | Dexn _ | Duse _ ->
        assert false
  in
  let uc = List.fold_left add_decl uc m.pth_decl in
  Typing.close_theory loc mt uc

let add_theory_module lib path (mm, mt) = function
  | Ptheory th -> mm, add_theory lib path mt th
  | Pmodule _m -> assert false (*TODO*)

