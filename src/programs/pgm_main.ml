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
open Pgm_env

let type_and_wp ?(type_only=false) env gl dl =
  let decl gl d = if type_only then gl else Pgm_wp.decl gl d in
  let add gl d =
    let gl, dl = Pgm_typing.decl env gl d in
    List.fold_left decl gl dl
  in
  List.fold_left add gl dl

let read_channel env file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let dl = Pgm_lexer.parse_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Theory.Mnm.empty
  else begin
    let type_only = Debug.test_flag Typing.debug_type_only in
    let uc = Theory.create_theory (Ident.id_fresh "Pgm") in
    let th = Env.find_theory env ["programs"] "Prelude" in
    let uc = Theory.use_export uc th in
    let gl = empty_env uc in
    let gl = type_and_wp ~type_only env gl dl in
    if type_only then
      Theory.Mnm.empty
    else begin
      let th = Theory.close_theory gl.uc in
      Theory.Mnm.add "Pgm" th Theory.Mnm.empty
    end
  end

let () = Env.register_format "whyml" ["mlw"] read_channel

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
