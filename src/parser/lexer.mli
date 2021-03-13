(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val parse_term : Lexing.lexbuf -> Ptree.term

val parse_expr : Lexing.lexbuf -> Ptree.expr

val parse_decl : Lexing.lexbuf -> Ptree.decl

val parse_term_list: Lexing.lexbuf -> Ptree.term list

val parse_qualid: Lexing.lexbuf -> Ptree.qualid

val parse_list_qualid: Lexing.lexbuf -> Ptree.qualid list

val parse_list_ident: Lexing.lexbuf -> Ptree.ident list

val parse_mlw_file: Lexing.lexbuf -> Ptree.mlw_file

val read_channel: Env.env -> Env.pathname -> string -> in_channel ->
  Pmodule.mlw_file

(* Name of the registered format for whyml *)
val whyml_format: Env.fformat

(*
val parse_program_file : Ptree.incremental -> Lexing.lexbuf -> unit
*)
