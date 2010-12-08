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

(* main module for whyl *)

open Format
open Why
open Ptree
open Pgm_ptree
open Pgm_module

let add_module ?(type_only=false) env tm m =
  ignore (type_only);
  let id = m.mod_name in
  let uc = create_module (Ident.id_user id.id id.id_loc) in
  let _uc = List.fold_left (Pgm_typing.decl env) uc m.mod_decl in
  tm

let read_channel env file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Pgm_lexer.parse_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Theory.Mnm.empty
  else begin
    let type_only = Debug.test_flag Typing.debug_type_only in
    List.fold_left (add_module ~type_only env) Theory.Mnm.empty ml
  (*   let uc = Theory.create_theory (Ident.id_fresh "Pgm") in *)
  (*   let th = Env.find_theory env ["programs"] "Prelude" in *)
  (*   let uc = Theory.use_export uc th in *)
  (*   let gl = empty_env uc in *)
  (*   let gl = type_and_wp ~type_only env gl dl in *)
  (*   if type_only then *)
  (*     Theory.Mnm.empty *)
  (*   else begin *)
  (*     let th = Theory.close_theory gl.uc in *)
  (*     Theory.Mnm.add "Pgm" th Theory.Mnm.empty *)
  (*   end *)
  end

let () = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
