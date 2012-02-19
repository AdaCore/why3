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

(* main module for whyl *)

open Format
open Why3
open Util
open Ident
open Theory
open Typing
open Ptree
open Pgm_module

let debug_extraction = Debug.register_flag "extraction"

exception ClashModule of string

let () = Exn_printer.register (fun fmt e -> match e with
  | ClashModule m -> fprintf fmt "clash with previous module %s" m
  | _ -> raise e)

let add_theory env path lenv m =
  let id = m.pth_name in
  let loc = id.id_loc in
  let env = Lexer.library_of_env (Env.env_of_library env) in
  let th = Theory.create_theory ~path (Denv.create_user_id id) in
  let rec add_decl th = function
    | Dlogic d ->
        Typing.add_decl env lenv th d
    | Dnamespace (loc, name, import, dl) ->
        let th = Theory.open_namespace th in
        let th = List.fold_left add_decl th dl in
        Typing.close_namespace loc import name th
    | Dlet _ | Dletrec _ | Dparam _ | Dexn _ | Duse _ -> assert false
  in
  let th = List.fold_left add_decl th m.pth_decl in
  close_theory loc lenv th

let add_module ?(type_only=false) env path (ltm, lmod) m =
  let id = m.mod_name in
  let loc = id.id_loc in
  if Mstr.mem id.id lmod then raise (Loc.Located (loc, ClashModule id.id));
  let wp = not type_only in
  let uc = create_module ~path (Ident.id_user id.id loc) in
  let logic_env = Lexer.library_of_env (Env.env_of_library env) in
  let prelude = Env.read_lib_theory logic_env ["bool"] "Bool" in
  let uc = use_export_theory uc prelude in
  let uc = List.fold_left (Pgm_typing.decl ~wp env ltm lmod) uc m.mod_decl in
  let md = close_module uc in
  if Debug.test_flag debug_extraction then Pgm_ocaml.extract_module path md;
  Mstr.add ("WP " ^ id.id) md.m_pure ltm, (* avoids a theory/module clash *)
  Mstr.add id.id md lmod

let add_theory_module ?(type_only=false) env path (ltm, lmod) = function
  | Ptheory t -> add_theory env path ltm t, lmod
  | Pmodule m -> add_module ~type_only env path (ltm, lmod) m

let retrieve env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Lexer.parse_program_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Mstr.empty, Mstr.empty
  else
    let type_only = Debug.test_flag Typing.debug_type_only in
    List.fold_left (add_theory_module ~type_only env path)
      (Mstr.empty, Mstr.empty) ml

let read_channel env path file c =
  let tm, mm = retrieve env path file c in
  mm, tm

let library_of_env = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
