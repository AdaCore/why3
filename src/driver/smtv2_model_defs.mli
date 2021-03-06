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

open Wstdlib
open Model_parser

type ident = string

type typ = string

type term =
  | Sval of model_value
  | Var of ident
  | Prover_var of typ * ident
  | Apply of (string * term list)
  | Array of array
  | Ite of term * term * term
  | Let of (string * term) list * term
  (* | Record of string * ((ident * term) list) *)
  | To_array of term

and array =
  | Avar of ident (* Used by let-bindings only *)
  | Aconst of term
  | Astore of array * term * term

type definition =
  | Function of (ident * typ option) list * typ option * term
  | Term of term (* corresponding value of a term *)
  | Noelement

val add_element: (string * definition) option ->
  definition Mstr.t -> definition Mstr.t

val substitute: (string * term) list -> term -> term
(** Substitute variables by terms. Used for let bindings of z3 *)

val print_term : term Pp.pp
val print_definition : definition Pp.pp
