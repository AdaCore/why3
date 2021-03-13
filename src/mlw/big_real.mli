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

type real

(* Exception raised when intervals do not allow decision of a comparison
   function. For example, equality on non-singleton intervals. *)
exception Undetermined

val init: int -> int -> int -> unit

val print_real: Format.formatter -> real -> unit

val real_from_str: string -> real
val real_from_fraction: string -> string -> real

(* Real operations *)
val neg: real -> real
val add: real -> real -> real
val mul: real -> real -> real
val div: real -> real -> real
val sqrt: real -> real
val exp: real -> real
val log: real -> real

(* Real comparisons *)
val eq: real -> real -> bool
val lt: real -> real -> bool
val le: real -> real -> bool
val gt: real -> real -> bool
val ge: real -> real -> bool

(* Constants *)
val pi: unit -> real
