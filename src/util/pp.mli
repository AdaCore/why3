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

(*i $Id: pp.mli,v 1.22 2009-10-19 11:55:33 bobot Exp $ i*)

open Format

val print_option : (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_option_or_default :
  string -> (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_list_pre :
  (formatter -> unit -> unit) ->
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list_suf :
  (formatter -> unit -> unit) ->
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list :
  (formatter -> unit -> unit) ->
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list_or_default :
  string -> (formatter -> unit -> unit) ->
  (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
val print_list_par :
  (Format.formatter -> unit -> 'a) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'b list -> unit
val print_list_delim :
  start:(Format.formatter -> unit -> unit) ->
  stop:(Format.formatter -> unit -> unit) ->
  sep:(Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'b list -> unit

val print_pair_delim :
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a * 'b -> unit
(** [print_pair_delim left_delim middle_delim right_delim] *)

val print_pair :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a * 'b -> unit

val print_iter1 :
  (('a -> unit) -> 'b -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'b -> unit

val print_iter2:
  (('a -> 'b -> unit) -> 'c -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter -> 'c -> unit
(**  [print_iter2 iter sep1 sep2 print1 print2 fmt t]
     iter iterator on [t : 'c]
     print1 k sep2 () print2 v sep1 () print1  sep2 () ...
*)

val print_iter22:
  (('a -> 'b -> unit) -> 'c -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> 'b -> unit) ->
  Format.formatter -> 'c -> unit
(**  [print_iter22 iter sep print fmt t]
     iter iterator on [t : 'c]
     print k v sep () print k v sep () ...
*)

(** formatted: string which is formatted "@ " allow to cut the line if
    too long *)
type formatted = (unit, unit, unit, unit, unit, unit) format6
val empty_formatted : formatted

val space : formatter -> unit -> unit
val alt : formatter -> unit -> unit
val alt2 : formatter -> unit -> unit
val newline : formatter -> unit -> unit
val newline2 : formatter -> unit -> unit
val dot : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val star : formatter -> unit -> unit
val simple_comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val colon : formatter -> unit -> unit
val underscore : formatter -> unit -> unit
val slash : formatter -> unit -> unit
val equal : formatter -> unit -> unit
val arrow : formatter -> unit -> unit
val lbrace : formatter -> unit -> unit
val rbrace : formatter -> unit -> unit
val lsquare : formatter -> unit -> unit
val rsquare : formatter -> unit -> unit
val lparen : formatter -> unit -> unit
val rparen : formatter -> unit -> unit
val lchevron : formatter -> unit -> unit
val rchevron : formatter -> unit -> unit
val nothing : formatter -> 'a -> unit
val string : formatter -> string -> unit
val float : formatter -> float -> unit
val int : formatter -> int -> unit
val constant_string : string -> formatter -> unit -> unit
val formatted : formatter -> formatted -> unit
val constant_formatted : formatted -> formatter -> unit -> unit
val print0 : formatter -> unit -> unit
val hov : int -> (formatter -> 'a -> unit) -> formatter -> 'a -> unit
val indent : int -> (formatter -> 'a -> unit) -> formatter -> 'a -> unit
(** add the indentation at the first line *)

val add_flush : (formatter -> 'a -> unit) -> formatter -> 'a -> unit

val asd : (formatter -> 'a -> unit) -> (formatter -> 'a -> unit)
(** add string delimiter  " " *)

val open_formatter : ?margin:int -> out_channel -> formatter
val close_formatter : formatter -> unit
val open_file_and_formatter : ?margin:int -> string -> out_channel * formatter
val close_file_and_formatter : out_channel * formatter -> unit
val print_in_file_no_close :
  ?margin:int -> (Format.formatter -> unit) -> string -> out_channel
val print_in_file : ?margin:int -> (Format.formatter -> unit) -> string -> unit


val print_list_opt :
  (formatter -> unit -> unit) ->
  (formatter -> 'a -> bool) -> formatter -> 'a list -> bool


val string_of : ?max_boxes:int ->
  (Format.formatter -> 'a -> unit) -> 'a -> string

val string_of_wnl : (Format.formatter -> 'a -> unit) -> 'a -> string
  (** same as {!string_of} but without newline *)

val wnl : Format.formatter -> unit

val sprintf :
  ('b,  formatter, unit, string) Pervasives.format4 -> 'b

val sprintf_wnl :
  ('b,  formatter, unit, string) Pervasives.format4 -> 'b

val html_char : Format.formatter -> char -> unit
val html_string : Format.formatter -> string -> unit
  (** formats the string by escaping special HTML characters
      quote, double quote, <, > and & *)


module Ansi :
sig
  val set_column : Format.formatter -> int -> unit
end

type formatter = Format.formatter
