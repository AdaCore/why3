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

(** Helpers for formatted pretty-printing *)

open Format

type 'a pp = formatter -> 'a -> unit

val print_option : 'a pp -> 'a option pp
val print_option_or_default : string -> 'a pp -> 'a option pp
val print_list_pre : unit pp -> 'a pp -> 'a list pp
val print_list_suf : unit pp -> 'a pp -> 'a list pp
val print_list : unit pp -> 'a pp -> 'a list pp
val print_list_or_default : string -> unit pp -> 'a pp -> 'a list pp
val print_list_par : (formatter -> unit -> 'a) -> 'b pp -> 'b list pp
val print_list_next : unit pp -> (bool -> 'a pp) -> 'a list pp
val print_list_delim :
  start:unit pp -> stop:unit pp -> sep:unit pp -> 'b pp -> 'b list pp

val print_pair_delim :
  unit pp -> unit pp -> unit pp -> 'a pp -> 'b pp -> ('a * 'b) pp
(** [print_pair_delim left_delim middle_delim right_delim] *)
val print_pair : 'a pp -> 'b pp -> ('a * 'b) pp

val print_iter1 :
  (('a -> unit) -> 'b -> unit) -> unit pp -> 'a pp -> 'b pp

val print_iter2:
  (('a -> 'b -> unit) -> 'c -> unit) ->
  unit pp -> unit pp -> 'a pp -> 'b pp -> 'c pp
(**  [print_iter2 iter sep1 sep2 print1 print2 fmt t]
     iter iterator on [t : 'c]
     print1 k sep2 () print2 v sep1 () print1  sep2 () ...
*)

val print_iter22:
  (('a -> 'b -> unit) -> 'c -> unit) ->
  unit pp ->
  (formatter -> 'a -> 'b -> unit) ->
  'c pp
(**  [print_iter22 iter sep print fmt t]
     iter iterator on [t : 'c]
     print k v sep () print k v sep () ...
*)

(** formatted: string which is formatted "@ " allow to cut the line if
    too long *)
type formatted = (unit, unit, unit, unit, unit, unit) format6
val empty_formatted : formatted

val space : unit pp
val alt : unit pp
val alt2 : unit pp
val newline : unit pp
val newline2 : unit pp
val dot : unit pp
val comma : unit pp
val star : unit pp
val simple_comma : unit pp
val semi : unit pp
val colon : unit pp
val underscore : unit pp
val slash : unit pp
val equal : unit pp
val arrow : unit pp
val lbrace : unit pp
val rbrace : unit pp
val lsquare : unit pp
val rsquare : unit pp
val lparen : unit pp
val rparen : unit pp
val lchevron : unit pp
val rchevron : unit pp
val nothing : 'a pp
val string : string pp
val float : float pp
val int : int pp
val constant_string : string -> unit pp
val formatted : formatter -> formatted -> unit
val constant_formatted : formatted -> unit pp
val print0 : unit pp
val hov : int -> 'a pp -> 'a pp
val indent : int -> 'a pp -> 'a pp
(** add the indentation at the first line *)

val add_flush : 'a pp -> 'a pp

val asd : 'a pp -> 'a pp
(** add string delimiter  " " *)

val open_formatter : ?margin:int -> out_channel -> formatter
val close_formatter : formatter -> unit
val open_file_and_formatter : ?margin:int -> string -> out_channel * formatter
val close_file_and_formatter : out_channel * formatter -> unit
val print_in_file_no_close :
  ?margin:int -> (formatter -> unit) -> string -> out_channel
val print_in_file : ?margin:int -> (formatter -> unit) -> string -> unit


val print_list_opt :
  unit pp -> (formatter -> 'a -> bool) -> formatter -> 'a list -> bool


val string_of : ?max_boxes:int -> 'a pp -> 'a -> string

val string_of_wnl : 'a pp -> 'a -> string
  (** same as {!string_of} but without newline *)

val wnl : formatter -> unit

val sprintf :
  ('b,  formatter, unit, string) Pervasives.format4 -> 'b

val sprintf_wnl :
  ('b,  formatter, unit, string) Pervasives.format4 -> 'b

val html_char : char pp
val html_string : string pp
  (** formats the string by escaping special HTML characters
      quote, double quote, <, > and & *)


module Ansi :
sig
  val set_column : formatter -> int -> unit
end

type formatter = Format.formatter
