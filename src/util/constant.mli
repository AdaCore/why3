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

open Format
open Number

type constant =
  | ConstInt  of int_constant
  | ConstReal of real_constant
  | ConstStr  of string
[@@deriving sexp_of]

val compare_const : ?structural:bool -> constant -> constant -> int
(** if [structural] then it is structural comparison, two
   mathematically equal values might differ; otherwise. mathematical
   values are compared *)

val int_const : ?il_kind:int_literal_kind -> BigInt.t -> constant
val int_const_of_int : int -> constant
val real_const : ?pow2:BigInt.t -> ?pow5:BigInt.t -> BigInt.t -> constant
val string_const : string -> constant

(** Pretty-printing *)

type escape_map = char -> string

val default_escape     : escape_map
val unsupported_escape : escape_map
val escape             : escape_map -> string -> string

val print_string_constant : escape_map -> formatter -> string -> unit
val print_string_def  : formatter -> string -> unit

val print : number_support -> escape_map -> formatter -> constant -> unit
val print_def : formatter -> constant -> unit
