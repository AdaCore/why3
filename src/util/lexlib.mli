(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** common functions to be used in lexers/parsers *)

val comment : Lexing.lexbuf -> unit

val string : Lexing.lexbuf -> string

val update_loc : Lexing.lexbuf -> string option -> int -> int -> unit

val backjump : Lexing.lexbuf -> int -> unit

val remove_leading_plus : string -> string

val remove_underscores : string -> string

val illegal_character : char -> Lexing.lexbuf -> 'a
