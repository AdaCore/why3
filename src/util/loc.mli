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

(** Source locations *)

open Format

(** {2 Lexing locations} *)

val current_offset : int ref
val reloc : Lexing.position -> Lexing.position
val set_file : string -> Lexing.lexbuf -> unit

val transfer_loc : Lexing.lexbuf -> Lexing.lexbuf -> unit

(** {2 locations in files} *)

type position
[@@deriving sexp_of]

val extract : Lexing.position * Lexing.position -> position
val join : position -> position -> position

val dummy_position : position

val user_position : string -> int -> int -> int -> position

val get : position -> string * int * int * int

val compare : position -> position -> int
val equal : position -> position -> bool
val hash : position -> int

val gen_report_position : formatter -> position -> unit

val report_position : formatter -> position -> unit

(** {2 located exceptions} *)

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

(** {2 located error messages} *)

exception Message of string

val errorm: ?loc:position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val with_location: (Lexing.lexbuf -> 'a) -> (Lexing.lexbuf -> 'a)

val get_multiline : position -> string * (int * int) * (int * int)
(** Returns [filename, (bline, bcol), (eline, ecol)] of a position.

    Currently, this function re-reads the file to determine the line and column of the end
    of multiline positions. Subsequent calls for positions in the same file will not require
    re-reading the file. The function fails if the file does not exist. *)
