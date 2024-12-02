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

(** {1 Source locations} *)


open Format

(** {2 Locations in files}

In Why3, source locations represent a part of a file, denoted by a
starting point and an end point. Both of these points are
represented by a line number and a column number.

So far, line numbers start with 1 and column number start with 0.
(See {{:https://gitlab.inria.fr/why3/why3/-/issues/706}this issue}.)

*)

type position
[@@deriving sexp]

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

type warning_id
(** warning identifiers *)

val register_warning : string -> Pp.formatted -> warning_id
(** [register_warning name desc] registers a new warning under the
   given [name] with the given [desc]ription. *)

val warning: warning_id ->
  ?loc:position -> ('b, Format.formatter, unit, unit) format4 -> 'b
(** [warning ~id ~loc fmt] emits a warning in the given formattter
   [fmt]. Adds the location [loc] if it is given. Emits nothing if the
   [id] is given and disabled, with one of the functions below. *)

val without_warning : warning_id -> (unit -> 'a) -> 'a
(** Given a warning identifier, execute an inner operation with the
   warning temporarily disabled. *)

val disable_warning : warning_id -> unit
(** [disable_warning id] globally disables the warning with this
   [id]. *)

val set_warning_hook: (?loc:position -> string -> unit) -> unit
(** The default behavior is to emit warning on standard error,
   with position on a first line (if any) and message on a second line.
   This can be changed using this hook. *)

(** {2 Command line arguments} *)

module Args : sig
  type spec = Getopt.opt

  val desc_warning_list : spec
  (** Option for printing the list of warning flags. *)

  val option_list : unit -> bool
  (** Print the list of flags if requested (in this case return [true]).
      You should run this function after the plugins have been loaded. *)

  val desc_no_warn : spec
  (** Option for specifying a warning flag to set. *)

  val set_flags_selected : ?silent:bool -> unit -> unit
  (** Set the flags selected by warning or a shortcut.
      When called before the plugins are loaded, pass [~silent:true] to
      prevent errors due to unknown plugin flags. *)
end

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
