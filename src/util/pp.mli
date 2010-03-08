(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: pp.mli,v 1.22 2009-10-19 11:55:33 bobot Exp $ i*)

open Format

val print_option : (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
val print_option_or_default :
  string -> (formatter -> 'a -> unit) -> formatter -> 'a option -> unit
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
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'b list -> unit

val print_pair_delim :
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> unit -> unit) ->
  (Format.formatter -> 'a -> unit) -> 
  (Format.formatter -> 'b -> unit) -> Format.formatter -> 'a * 'b -> unit
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

val space : formatter -> unit -> unit
val alt : formatter -> unit -> unit
val newline : formatter -> unit -> unit
val newline2 : formatter -> unit -> unit
val dot : formatter -> unit -> unit
val comma : formatter -> unit -> unit
val simple_comma : formatter -> unit -> unit
val semi : formatter -> unit -> unit
val underscore : formatter -> unit -> unit
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
val constant_string : string -> formatter -> unit -> unit
val hov : int -> formatter -> ('a -> unit) -> 'a -> unit

val open_formatter : ?margin:int -> out_channel -> formatter
val close_formatter : formatter -> unit
val open_file_and_formatter : ?margin:int -> string -> out_channel * formatter
val close_file_and_formatter : out_channel * formatter -> unit
val print_in_file_no_close : ?margin:int -> (Format.formatter -> unit) -> string -> out_channel
val print_in_file : ?margin:int -> (Format.formatter -> unit) -> string -> unit
