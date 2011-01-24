(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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
open Theory
open Ptree
open Pgm_module

exception ClashModule of string

let () = Exn_printer.register (fun fmt e -> match e with
  | ClashModule m -> fprintf fmt "clash with previous module %s" m
  | _ -> raise e)

let add_module ?(type_only=false) env penv (ltm, lmod) m =
  let id = m.mod_name in
  let loc = id.id_loc in
  if Mnm.mem id.id lmod then raise (Loc.Located (loc, ClashModule id.id));
  let wp = not type_only in
  let uc = create_module (Ident.id_user id.id loc) in
  let prelude = Env.find_theory env ["programs"] "Prelude" in
  let uc = use_export_theory uc prelude in
  let uc = 
    List.fold_left (Pgm_typing.decl ~wp env penv ltm lmod) uc m.mod_decl 
  in
  let m = close_module uc in
  Mnm.add id.id m.m_th ltm,
  Mnm.add id.id m lmod

let retrieve penv file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Lexer.parse_program_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Mnm.empty, Mnm.empty
  else
    let type_only = Debug.test_flag Typing.debug_type_only in
    let env = Pgm_env.get_env penv in
    List.fold_left (add_module ~type_only env penv) 
      (Mnm.empty, Mnm.empty) ml

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
  let tm, _ = retrieve penv file c in
  tm

let () = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
