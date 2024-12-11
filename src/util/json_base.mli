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

val list :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
(* provided a printer for elements, print a json list of these elements. In the
   case of the empty list, print the json empty list [] *)

(* for more complex applications it may be convenient to build a an
   explicit JSON object. Use this type for that and the print_json
   function to print it *)
type json =
  | Record of (string * json) list
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

val get_string_field : json -> string -> string
val get_int_field : json -> string -> int
val get_list_field : json -> string -> json list
val get_float_field : json -> string -> float
val get_bool_field : json -> string -> bool

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
