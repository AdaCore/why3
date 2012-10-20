(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format

type integer_format = (string -> unit, Format.formatter, unit) format
type real_format = (string -> string -> string -> unit, Format.formatter, unit) format
type part_real_format = (string -> string -> unit, Format.formatter, unit) format
type dec_real_format =
  | PrintDecReal of part_real_format * real_format
type frac_real_format =
  | PrintFracReal of integer_format * part_real_format * part_real_format

type 'a number_support_kind =
  | Number_unsupported
  | Number_default
  | Number_custom of 'a

type integer_support_kind = integer_format number_support_kind

type number_support = {
  long_int_support : bool;
  dec_int_support : integer_support_kind;
  hex_int_support : integer_support_kind;
  oct_int_support : integer_support_kind;
  bin_int_support : integer_support_kind;
  def_int_support : integer_support_kind;
  dec_real_support : dec_real_format number_support_kind;
  hex_real_support : real_format number_support_kind;
  frac_real_support : frac_real_format number_support_kind;
  def_real_support : integer_support_kind;
}

val print : number_support -> formatter -> Term.constant -> unit
