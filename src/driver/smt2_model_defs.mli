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

open Stdlib

type variable = string

type float_type =
  | Plus_infinity
  | Minus_infinity
  | Plus_zero
  | Minus_zero
  | Not_a_number
  | Float_value of string * string * string

type array =
  | Const of term
  | Store of array * term * term

and term =
  | Integer of string
  | Decimal of (string * string)
  | Float of float_type
  | Other of string
  | Array of array
  | Bitvector of string
  | Boolean of bool
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
  | Ite of term * term * term * term
  | Record of int * (term list)
  | Discr of int * (term list)
  | To_array of term

type definition =
  | Function of variable list * term
  | Term of term (* corresponding value of a term *)
  | Noelement

(* Type returned by parsing of model.
   An hashtable that makes a correspondence between names (string) and
   associated definition (complex stuff) *)
(* The boolean is true when the term has no external variable *)
type correspondence_table = (bool * definition) Mstr.t

val add_element: (string * definition) option ->
  correspondence_table -> bool -> correspondence_table


val make_local: variable list -> term -> term

val print_term: Format.formatter -> term -> unit
val print_def: Format.formatter -> definition -> unit

val build_record_discr: term list -> term

(* Used for let bindings of z3 *)
val substitute: (string * term) list -> term -> term
