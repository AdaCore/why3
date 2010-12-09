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
open Util
open Ident
open Ptree
open Pgm_ptree
open Pgm_module

let add_module ?(type_only=false) env lmod m =
  let wp = not type_only in
  let id = m.mod_name in
  let uc = create_module (Ident.id_user id.id id.id_loc) in
  let uc = List.fold_left (Pgm_typing.decl ~wp env lmod) uc m.mod_decl in
  let m = close_module uc in
  Mstr.add id.id m lmod

let read_channel env file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Pgm_lexer.parse_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Theory.Mnm.empty
  else begin
    let type_only = Debug.test_flag Typing.debug_type_only in
    let mm = List.fold_left (add_module ~type_only env) Mstr.empty ml in
    Mstr.fold 
      (fun _ m tm -> Theory.Mnm.add m.m_name.id_string m.m_th tm) 
      mm Theory.Mnm.empty
  end

let () = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
