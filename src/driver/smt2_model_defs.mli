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

type array =
  | Const of term
  | Store of array * term * term

and term =
  | Integer of string
  | Decimal of (string * string)
  | Fraction of (string * string)
  | Float of Model_parser.float_type
  | Apply of (string * term list)
  | Other of string
  | Array of array
  | Bitvector of string
  | Boolean of bool
  | Cvc4_Variable of variable
  | Function_Local_Variable of variable
  | Variable of variable
  | Ite of term * term * term * term
  | Record of string * ((string * term) list)
  | To_array of term

type definition =
  | Function of (variable * string option) list * term
  | Term of term (* corresponding value of a term *)
  | Noelement

(* Type returned by parsing of model.
   An hashtable that makes a correspondence between names (string) and
   associated definition (complex stuff) *)
(* The boolean is true when the term has no external variable *)
type correspondence_table = (bool * definition) Mstr.t

val add_element: (string * definition) option ->
  correspondence_table -> bool -> correspondence_table


val make_local: (variable * string option) list -> term -> term

val print_term: Format.formatter -> term -> unit
val print_def: Format.formatter -> definition -> unit

(* Used for let bindings of z3 *)
val substitute: (string * term) list -> term -> term
