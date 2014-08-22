(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val library_of_env : Env.env -> unit Env.library

val parse_logic_file :
  Env.env -> Env.pathname -> Lexing.lexbuf -> Theory.theory Stdlib.Mstr.t

val parse_program_file :
  Ptree.incremental -> Lexing.lexbuf -> unit

val token_counter : Lexing.lexbuf -> int * int
