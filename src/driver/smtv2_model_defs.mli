(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
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

type constant_bv = {
  bv_value : BigInt.t;
  bv_length : int;
  bv_verbatim : string;
}

type constant_real = {
  real_neg : bool; (* true for negative real numbers *)
  real_int : string;
  real_frac : string;
}

type constant_float =
  | Fplusinfinity
  | Fminusinfinity
  | Fpluszero
  | Fminuszero
  | Fnan
  | Fnumber of { sign : constant_bv; exp : constant_bv; mant : constant_bv }

type constant =
  | Cint of BigInt.t
  | Cdecimal of constant_real
  | Cfraction of constant_real * constant_real
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
  | Tunparsed of string

and var_binding = symbol * term
and array_elements = { array_indices : (term * term) list; array_others : term }

type function_def = (symbol * sort) list * sort * term

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
