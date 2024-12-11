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

val parse : string -> in_channel -> Py_ast.file
val parse_term : Lexing.lexbuf -> Why3.Ptree.term
val parse_term_list : Lexing.lexbuf -> Why3.Ptree.term list
val parse_list_ident : Lexing.lexbuf -> Why3.Ptree.ident list
