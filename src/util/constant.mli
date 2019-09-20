(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
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

val compare_const : constant -> constant -> int
(** structural comparison; two mathematically equal values might differ *)

val int_const : BigInt.t -> constant
val int_const_of_int : int -> constant

val real_const : ?pow2:BigInt.t -> ?pow5:BigInt.t -> BigInt.t -> constant

(** Pretty-printing *)

val print_string_constant : formatter -> string -> unit

val print : number_support -> formatter -> constant -> unit

val print_constant : formatter -> constant -> unit
