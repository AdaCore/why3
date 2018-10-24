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

open Wstdlib

type variable = string

(* Simple counterexample that already represent a complete value *)
type simple_value =
  | Integer of string
  | Decimal of (string * string)
  | Fraction of (string * string)
  | Float of Model_parser.float_type
  | Other of string
  | Bitvector of string
  | Boolean of bool

type array =
  (* Array_var is used by let-bindings only *)
  | Array_var of variable
  | Const of term
  | Store of array * term * term

and term =
  | Sval of simple_value
  | Apply of (string * term list)
  | Array of array
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
  | Ite of term * term * term * term
  | Record of string * ((string * term) list)
  | To_array of term
  (* TODO remove tree *)
  | Trees of (string * term) list

type definition =
  | Function of (variable * string option) list * term
  | Term of term (* corresponding value of a term *)
  | Noelement

val add_element: (string * definition) option ->
  definition Mstr.t -> definition Mstr.t

val make_local: (variable * string option) list -> term -> term

(* Used for let bindings of z3 *)
val substitute: (string * term) list -> term -> term
