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

(** {1 Source locations} *)


open Format

(** {2 Locations in files}

In Why3, source locations represent a part of a file, denoted by a
starting point and an end point. Both of these points are
represented by a line number and a column number.

So far, line numbers start with 1 and column number start with 0. [FIXME]

*)

type position
[@@deriving sexp_of]

val user_position : string -> int -> int -> int -> int -> position
(** [user_position f bl bc el ec] builds the source position for file
    [f], starting at line [bl] and character [bc] and ending at line
    [el] and character [ec]. *)

val dummy_position : position
(** Dummy source position. *)

val get : position -> string * int * int * int * int
(** [get p] returns the file, the line and character numbers of the
    beginning and the line and character numbers of the end of the
    given position. *)

val join : position -> position -> position
(** [join p1 p2] attempts to join positions [p1] and [p2],
    returning a position that covers both of them. This function
    assumes that the files are the same. *)


val compare : position -> position -> int
val equal : position -> position -> bool
val hash : position -> int

val pp_position : formatter -> position -> unit
(** [pp_position fmt loc] formats the position [loc] in the given
    formatter, in a human readable way, that is:
    - either ["filename", line l, characters bc--ec] if the position is on a single line,
    - or ["filename", line bl, character bc to line el, character ce] if the position is multi-line.

    The file name is not printed if empty. *)

val pp_position_no_file : formatter -> position -> unit
(** Similar to [pp_position] but do not show the file name. *)

(** {2 Helper functions about OCaml locations used in module [Lexing]} *)

val extract : Lexing.position * Lexing.position -> position
(** [extract p1 p2] build a source position from two OCaml lexing
   positions *)

val current_offset : int ref
val reloc : Lexing.position -> Lexing.position
(** [reloc l] returns the location with character num augmented by [!current_offset]. *)

val set_file : string -> Lexing.lexbuf -> unit
(** [set_file f lb] sets the file name to [f] in [lb]. *)

val transfer_loc : Lexing.lexbuf -> Lexing.lexbuf -> unit
(** [transfer_loc from to] sets the [lex_start_p] and [lex_curr_p]
   fields of [to] to the ones of [from]. *)

(** {2 Located warnings} *)

val warning:
  ?loc:position -> ('b, Format.formatter, unit, unit) format4 -> 'b

(** The default behavior is to emit warning on standard error,
   with position on a first line (if any) and message on a second line.
   This can be changed using the following function. *)

val set_warning_hook: (?loc:position -> string -> unit) -> unit

(** {2 Located exceptions} *)

exception Located of position * exn

val try1: ?loc:position -> ('a -> 'b) -> ('a -> 'b)
val try2: ?loc:position -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
val try3: ?loc:position -> ('a -> 'b -> 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)

val try4: ?loc:position ->
  ('a -> 'b -> 'c -> 'd -> 'e) -> ('a -> 'b -> 'c -> 'd -> 'e)

val try5: ?loc:position ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f) -> ('a -> 'b -> 'c -> 'd -> 'e -> 'f)

val try6: ?loc:position ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g)

val try7: ?loc:position ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h)

val error: ?loc:position -> exn -> 'a

(** {2 Located error messages} *)

exception Message of string

val errorm: ?loc:position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val with_location: (Lexing.lexbuf -> 'a) -> (Lexing.lexbuf -> 'a)
