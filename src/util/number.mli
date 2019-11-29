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

(** General functions for representations of numeric values *)

exception InvalidConstantLiteral of int * string

type int_value = BigInt.t

type int_literal_kind =
  ILitUnk | ILitDec | ILitHex | ILitOct | ILitBin

type int_constant = {
  il_kind : int_literal_kind;
  il_int  : int_value;
}

type real_value = private {
  rv_sig  : BigInt.t;
  rv_pow2 : BigInt.t;
  rv_pow5 : BigInt.t;
}

type real_literal_kind =
  RLitUnk | RLitDec of int | RLitHex of int

type real_constant = {
  rl_kind : real_literal_kind;
  rl_real : real_value
}

val neg_int : int_constant -> int_constant
val abs_int : int_constant -> int_constant

val neg_real : real_constant -> real_constant
val abs_real : real_constant -> real_constant

val compare_real : real_value -> real_value -> int
(** structural comparison; two ordered values might compare differently *)

val int_literal : int_literal_kind -> neg:bool -> string -> int_constant

val real_literal : radix:int -> neg:bool -> int:string -> frac:string -> exp:string option -> real_constant
val real_value : ?pow2:BigInt.t -> ?pow5:BigInt.t -> BigInt.t -> real_value

(** Pretty-printing with conversion *)

type default_format =
  Format.formatter -> string -> unit

type integer_format =
  Format.formatter -> BigInt.t -> unit

type real_format =
  Format.formatter -> string -> string -> string option -> unit

type two_strings_format =
  Format.formatter -> string -> string -> unit

type frac_real_format =
  (Format.formatter -> string -> unit) * two_strings_format * two_strings_format

type delayed_format =
  Format.formatter -> (Format.formatter -> unit) -> unit

type number_support = {
  long_int_support  : [`Default|`Custom of default_format];
  negative_int_support : [`Default|`Custom of delayed_format];
  dec_int_support   : [`Default|`Custom of integer_format|`Unsupported of default_format];
  hex_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  oct_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  bin_int_support   : [`Default|`Custom of integer_format|`Unsupported];
  negative_real_support : [`Default|`Custom of delayed_format];
  dec_real_support  : [`Default|`Custom of real_format|`Unsupported];
  hex_real_support  : [`Default|`Custom of real_format|`Unsupported];
  frac_real_support : [`Custom of frac_real_format|`Unsupported of default_format];
}

val full_support : number_support

val print_int_constant : number_support -> formatter -> int_constant -> unit
val print_real_constant : number_support -> formatter -> real_constant -> unit

val print_in_base : int -> int option -> formatter -> BigInt.t -> unit
(** [print_in_base radix digits fmt i] prints the value of [i] in base
    [radix]. If digits is not [None] adds leading 0s to have [digits]
    characters.
    REQUIRES [i] non-negative *)

(** Range checking *)

val to_small_integer : int_constant -> int
(* may raise invalid_argument *)

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}

val create_range : BigInt.t -> BigInt.t -> int_range

exception OutOfRange of int_constant

val check_range : int_constant -> int_range -> unit
(** [check_range c ir] checks that [c] is in the range described
    by [ir], and raises [OutOfRange c] if not. *)


(** Float checking *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_constant

val compute_float : real_constant -> float_format -> BigInt.t * BigInt.t
(** [compute_float c fp] checks that [c] is a float literal
    representable in the format [fp]. Returns a pair [e,s] with
    [s] the significand (without the hidden bit), and [e] the biased
    exponent. Raises [NonRepresentableFloat c] exception otherwise. *)

val check_float : real_constant -> float_format -> unit
(** [check_float c fp] is the same as [compute_float c fp]
    but does not return any value. *)
