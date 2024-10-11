(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
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

val resolve_file : string -> string -> string
(** [resolve_file orig src] resolves the file name [src], a path name
    relative to the directory name of [orig] *)

val backjump : Lexing.lexbuf -> int -> unit
(** [backjump lexbuf n] rewinds the lexing buffer by [n] bytes, thus
    making it possible to tokenize the current buffer in a different way,
    e.g., shortest match instead of longest match.
    This requires the buffer to still contain these [n] bytes, which
    is only guaranteed if the current lexing rule matched at least
    [n] bytes. *)

val remove_leading_plus : string -> string

val remove_underscores : string -> string

val illegal_character : char -> Lexing.lexbuf -> 'a

val utf8_extra_bytes : char -> int
(** [utf8_extra_bytes c] returns the number of continuation bytes needed
    to turn a string starting by [c] into an UTF8 character. The function
    returns [-1] if [c] cannot be the first byte of an UTF-8 character. *)

val adjust_pos : Lexing.lexbuf -> int -> unit
(** [adjust_pos lexbuf n] reduces the current column number of [lexbuf]
    by [n]. This is especially useful if the current lexeme contains [n]
    less characters than bytes. *)

val adjust_pos_utf8 : Lexing.lexbuf -> string -> unit
(** [adjust_pos_utf8 lexbuf s] adjusts the current column number of [lexbuf]
    to account for the UTF-8 characters present in a substring [s] of the
    current lexeme. *)
