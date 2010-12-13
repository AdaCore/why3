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

let add_module ?(type_only=false) env penv lmod m =
  let wp = not type_only in
  let id = m.mod_name in
  let uc = create_module (Ident.id_user id.id id.id_loc) in
  let uc = List.fold_left (Pgm_typing.decl ~wp env penv lmod) uc m.mod_decl in
  let m = close_module uc in
  Mnm.add id.id m lmod

let retrieve penv file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Pgm_lexer.parse_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Mnm.empty
  else
    let type_only = Debug.test_flag Typing.debug_type_only in
    let env = Pgm_env.get_env penv in
    List.fold_left (add_module ~type_only env penv) Mnm.empty ml

let pgm_env_of_env =
  let h = Env.Wenv.create 17 in
  fun env -> 
    try 
      Env.Wenv.find h env 
    with Not_found -> 
      let penv = Pgm_env.create env retrieve in 
      Env.Wenv.set h env penv; 
      penv

let read_channel env file c =
  let penv = pgm_env_of_env env in
  let mm = retrieve penv file c in
  Mnm.fold 
    (fun _ m tm -> Theory.Mnm.add m.m_name.id_string m.m_th tm) 
    mm Theory.Mnm.empty

let () = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
