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

open Format

(** General functions for representations of numeric values *)

exception InvalidConstantLiteral of int * string

type integer_literal = private
  | IConstRaw of BigInt.t
  | IConstDec of string
  | IConstHex of string
  | IConstOct of string
  | IConstBin of string

type integer_constant = {
    ic_negative : bool;
    ic_abs : integer_literal;
  }

type real_literal = private
  | RConstDec of string * string * string option (* int / frac / exp *)
  | RConstHex of string * string * string option
  (** If you want to write the constant 1/3 you need to use the
      division function from the real theory *)

type real_constant = {
    rc_negative : bool;
    rc_abs : real_literal;
  }

type constant =
  | ConstInt  of integer_constant
  | ConstReal of real_constant

val is_negative : constant -> bool

val int_literal_dec : string -> integer_literal
val int_literal_hex : string -> integer_literal
val int_literal_oct : string -> integer_literal
val int_literal_bin : string -> integer_literal
(** these four functions construct integer constant terms from some
    string [s] of digits in the corresponding base. Exception
    InvalidConstantLiteral(base,s) is raised if [s] contains invalid
    characters for the given base. *)

val int_literal_raw : BigInt.t -> integer_literal

val int_const_of_int : int -> integer_constant
val int_const_of_big_int : BigInt.t -> integer_constant

val const_of_int : int -> constant
val const_of_big_int : BigInt.t -> constant

val real_const_dec : string -> string -> string option -> real_literal
(** [real_const_dec integer_part decimal_part exp] return the real that corresponds to
    "integer_part.decimal_part * 10^exp". By default exp is 0.
*)
val real_const_hex : string -> string -> string option -> real_literal

(** Pretty-printing *)

val print_constant : formatter -> constant -> unit

(** Pretty-printing with conversion *)

type integer_format =
  (string -> unit, Format.formatter, unit) format

type real_format =
  (string -> string -> string -> unit, Format.formatter, unit) format

type part_real_format =
  (string -> string -> unit, Format.formatter, unit) format

type dec_real_format =
  | PrintDecReal of part_real_format * real_format

type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Number_unsupported
  | Number_default
  | Number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type 'a negative_format =
  ((Format.formatter->'a->unit)->'a->unit, Format.formatter,unit) format

type number_support = {
  long_int_support  : bool;
  extra_leading_zeros_support : bool;
  negative_int_support  : (integer_literal negative_format) number_support_kind;
  dec_int_support   : integer_support_kind;
  hex_int_support   : integer_support_kind;
  oct_int_support   : integer_support_kind;
  bin_int_support   : integer_support_kind;
  def_int_support   : integer_support_kind;
  negative_real_support  : (real_literal negative_format) number_support_kind;
  dec_real_support  : dec_real_format number_support_kind;
  hex_real_support  : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support  : integer_support_kind;
}

val print : number_support -> formatter -> constant -> unit

val print_in_base : int -> int option -> formatter -> BigInt.t -> unit
(** [print_in_base radix digits fmt i] prints the value of [i] in base
    [radix]. If digits is not [None] adds leading 0s to have [digits]
    characters.
    REQUIRES [i] non-negative *)

(** Range checking *)

val to_small_integer : integer_literal -> int
(* may raise invalid_argument *)

val compute_int_literal : integer_literal -> BigInt.t
val compute_int_constant : integer_constant -> BigInt.t

type int_range = {
  ir_lower : BigInt.t;
  ir_upper : BigInt.t;
}

val create_range : BigInt.t -> BigInt.t -> int_range

exception OutOfRange of integer_constant

val check_range : integer_constant -> int_range -> unit
(** [check_range c ir] checks that [c] is in the range described
    by [ir], and raises [OutOfRange c] if not. *)


(** Float checking *)

type float_format = {
  fp_exponent_digits    : int;
  fp_significand_digits : int; (* counting the hidden bit *)
}

exception NonRepresentableFloat of real_literal

val compute_float : real_literal -> float_format -> BigInt.t * BigInt.t
(** [compute_float c fp] checks that [c] is a float literal
    representable in the format [fp]. Returns a pair [e,s] with
    [s] the significand (without the hidden bit), and [e] the biased
    exponent. Raises [NonRepresentableFloat c] exception otherwise. *)

val check_float : real_literal -> float_format -> unit
(** [check_float c fp] is the same as [compute_float c fp]
    but does not return any value. *)
