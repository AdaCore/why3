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

(* use the simple printer functions to quickly print some JSON *)

val string : Format.formatter -> string -> unit
(* print json string, that is add '"' to the front and back, and escape
   characters escaped in JSON string *)
val int : Format.formatter -> int -> unit
(* print an integer *)
val bool : Format.formatter -> bool -> unit
(* print an boolean *)
val float : Format.formatter -> float -> unit
(* print a floating point number *)
val standard_float : Format.formatter -> float -> unit
(* print a float in a format that cannot be mistaken for an integer (this makes
   communication with other tools easier).
*)

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

val convert_record : (string * 'a) list -> 'a Wstdlib.Mstr.t

(* for more complex applications it may be convenient to build a an
   explicit JSON object. Use this type for that and the print_json
   function to print it *)
type json =
  | Record of json Wstdlib.Mstr.t
  | Proj of json Wstdlib.Mstr.t
  | List of json list
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Null

val print_json : Format.formatter -> json -> unit

(** Convenience function that returns a field/part of json_value or return
    Not_found if not present *)

(* Get json fields. Return Not_found if no fields or field missing *)
val get_field: json -> string -> json

val get_string: json -> string
val get_int: json -> int
val get_list: json -> json list
val get_float: json -> float
val get_bool: json -> bool
val get_bool_opt: json -> bool -> bool

(* To parse a json value, use file Json_parser and function json_object. See
   end of session/Json_util.ml for an example use.
val parse : string -> value
 *)
