(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Model_parser

type variable = string

type term =
  | Sval of model_value
  | Apply of (string * term list)
  | Array of array
  | Var of variable
  | Function_var of variable (* Function parameter *)
  | Prover_var of variable (* Variable introduced by prover (e.g. @x or x!0) *)
  | Ite of term * term * term * term
  | Record of string * ((string * term) list)
  | To_array of term

and array =
  | Avar of variable (* Used by let-bindings only *)
  | Aconst of term
  | Astore of array * term * term

type definition =
  | Function of (variable * string option) list * term
  | Term of term (* corresponding value of a term *)
  | Noelement

val add_element: (string * definition) option ->
  definition Mstr.t -> definition Mstr.t

val make_local: (variable * string option) list -> term -> term
(** For a definition of function f, local variables being in vars_lists and the
    returned term being t, this function changes the term to give an appropriate
    tag to variables that are actually local. *)

val substitute: (string * term) list -> term -> term
(** Substitute variables by terms. Used for let bindings of z3 *)

val print_term : term Pp.pp
val print_definition : definition Pp.pp
