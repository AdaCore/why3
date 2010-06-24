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
open Pgm_env

let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Pgm_lexer.Error e ->
      fprintf fmt "lexical error: %a" Pgm_lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Typing.Error e ->
      Typing.report fmt e
  | Pgm_typing.Error e ->
      Pgm_typing.report fmt e
  | Denv.Error e ->
      Denv.report fmt e
  | Ty.TypeMismatch (ty1, ty2) as e ->
      eprintf "@[type mismatch: %a, %a@]@." 
	Pretty.print_ty ty1 Pretty.print_ty ty2;
      raise e
  | e ->
      raise e

let parse_only _env file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  ignore (Pgm_lexer.parse_file lb)

let type_and_wp ?(type_only=false) env gl dl =
  let decl gl d = if type_only then gl else Pgm_wp.decl gl d in
  let add gl d = 
    let gl, dl = Pgm_typing.decl env gl d in
    List.fold_left decl gl dl
  in
  List.fold_left add gl dl

let read_channel 
    ?(debug=false) ?(parse_only=false) ?(type_only=false) env file c =
  Pgm_typing.debug := debug;
  Pgm_wp.debug := debug;
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let dl = Pgm_lexer.parse_file lb in 
  if parse_only then 
    Theory.Mnm.empty
  else begin
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

let () =
  Env.register_format "whyml" ["mlw"] read_channel report

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
