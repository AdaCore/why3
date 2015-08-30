(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** common functions to be used in lexers/parsers *)

val newline : Lexing.lexbuf -> unit

val comment : Lexing.lexbuf -> unit

val string : Lexing.lexbuf -> string

val update_loc : Lexing.lexbuf -> string option -> int -> int -> unit

val remove_leading_plus : string -> string

val remove_underscores : string -> string

val has_prefix : string -> string -> bool
(** [has_prefix pref s] returns true if s [s] starts with prefix [pref] *)

val remove_prefix : string -> string -> string
(** [remove_prefix pref s] removes the prefix [pref] from [s]. Raises
    [Not_found if [s] does not start with [pref] *)
