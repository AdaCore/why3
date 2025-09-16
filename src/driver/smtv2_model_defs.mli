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

(* Based on SMT-LIB Standard: Version 2.6 *)

type symbol = S of string | Sprover of string
type index = Idxnumeral of BigInt.t | Idxsymbol of symbol
type identifier = Isymbol of symbol | Iindexedsymbol of symbol * index list

type sort =
  | Sstring
  | Sreglan
  | Sint
  | Sreal
  | Sroundingmode
  | Sbool
  | Sbitvec of int
  | Sfloatingpoint of int * int
  | Sarray of sort * sort
  | Ssimple of identifier
  | Smultiple of identifier * sort list

type constant_int = {
  constant_int_value: Number.int_constant;
  constant_int_verbatim: string
}

type constant_bv = {
  constant_bv_value : BigInt.t;
  constant_bv_length : int;
  constant_bv_verbatim : string;
}

type constant_real = {
  constant_real_value: Number.real_constant;
  constant_real_verbatim: string
}

type constant_frac = {
  constant_frac_num: constant_real;
  constant_frac_den: constant_real;
  constant_frac_verbatim: string
}

type constant_float_value =
  | Fplusinfinity
  | Fminusinfinity
  | Fpluszero
  | Fminuszero
  | Fnan
  | Fnumber of {
      constant_float_sign : constant_bv;
      constant_float_exp : constant_bv;
      constant_float_mant : constant_bv
    }

type constant_float = {
  const_float_exp_size : int;
  const_float_significand_size : int;
  const_float_val : constant_float_value
}

type constant =
  | Cint of constant_int
  | Creal of constant_real
  | Cfraction of constant_frac
  | Cbitvector of constant_bv
  | Cfloat of constant_float
  | Cbool of bool
  | Cstring of string

type qual_identifier = Qident of identifier | Qannotident of identifier * sort

type term =
  | Tconst of constant
  | Tvar of qual_identifier
  | Tapply of qual_identifier * term list
  | Tite of term * term * term
  | Tarray of sort * sort * array_elements
  | Tasarray of term
  | Tlet of var_binding list * term
  | Tforall of var_signature list * term
  | Tunparsed of string

and var_binding = symbol * term
and var_signature = symbol * sort
and array_elements = { array_indices : (term * term) list; array_others : term }

type function_def = var_signature list * sort * term

val sort_equal : sort -> sort -> bool
val print_index : Format.formatter -> index -> unit
val print_identifier : Format.formatter -> identifier -> unit
val print_sort : Format.formatter -> sort -> unit
val print_constant : Format.formatter -> constant -> unit
val print_qualified_identifier : Format.formatter -> qual_identifier -> unit
val print_term : Format.formatter -> term -> unit
val print_var_binding : Format.formatter -> var_binding -> unit
val print_array : Format.formatter -> array_elements -> unit
val print_function_def : Format.formatter -> function_def -> unit
