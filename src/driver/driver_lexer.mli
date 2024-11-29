(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val parse_file:
  Whyconf.main ->
  (string -> Lexing.lexbuf) -> Lexing.lexbuf -> Driver_ast.file
val parse_file_extract:
  Whyconf.main ->
  (string -> Lexing.lexbuf) -> Lexing.lexbuf -> Driver_ast.file_extract
