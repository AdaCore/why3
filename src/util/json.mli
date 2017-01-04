(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* use the simple printer functions to quickly print some JSON *)

val string : Format.formatter -> string -> unit
(* print json string, that is add '"' to the front and back, and escape '"' and
   '\' in the string *)
val int : Format.formatter -> int -> unit
(* print an integer *)
val bool : Format.formatter -> bool -> unit
(* print an boolean *)
val float : Format.formatter -> float -> unit
(* print an floating point number *)

val list :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
(* provided a printer for elements, print a json list of these elements. In the
   case of the empty list, print the json empty list [] *)

val map_bindings :
  ('a -> string) ->
  (Format.formatter -> 'b -> unit) ->
  Format.formatter ->
  ('a * 'b) list ->
  unit
(* arguments:
   * a mapping from keys to strings;
   * a printer of values
   * the formatter
   * a list of key,value pairs
  action: print the list of key-value pairs as a json record, if the list is
  empty, print the empty record *)

val print_json_field :
  string -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
(* given a field name, a value and a printer for the value, print a json
   mapping (field assignment). Do not print anything else. *)

(* for more complex applications it may be convenient to build a an
   explicit JSON object. Use this type for that and the print_json
   function to print it *)

type json =
  | Int of int
  | Float of float
  | Bool of bool
  | String of string
  | List of json list
  | Record of json Stdlib.Mstr.t

val print_json : Format.formatter -> json -> unit
