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

(** {1 Wrapper for big nums, implemented either with OCaml's [Nums] or [ZArith]} *)

type t
[@@deriving sexp]

val compare : t -> t -> int

(** {2 Constants} *)

val zero : t
val one : t
val of_int : int -> t

(** {2 Basic operations} *)

val succ : t -> t
val pred : t -> t
val add_int : int -> t -> t
val mul_int : int -> t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val minus : t -> t
val sign : t -> int

(** {2 Comparisons} *)

val eq : t -> t -> bool
val lt : t -> t -> bool
val gt : t -> t -> bool
val le : t -> t -> bool
val ge : t -> t -> bool

(** {2 Division and modulo operators}

{3 Euclidean division}

By convention, the modulo is always non-negative.
This implies that division rounds down when divisor is positive, and
rounds up when divisor is negative.
*)

val euclidean_div_mod : t -> t -> t * t
val euclidean_div : t -> t -> t
val euclidean_mod : t -> t -> t

(** {3 "Computer" division}

Division rounds toward zero, and thus [mod x y] has the same sign as [x].
*)

val computer_div_mod : t -> t -> t * t
val computer_div : t -> t -> t
val computer_mod : t -> t -> t

(** {2 min, max, abs} *)

val min : t -> t -> t
val max : t -> t -> t
val abs : t -> t

(** {2 Number of digits} *)

val num_digits : t -> int

(** {2 Power of small integers}

Second argument must be non-negative. *)

val pow_int_pos : int -> int -> t
val pow_int_pos_bigint : int -> t -> t

(** {2 Conversions} *)

val of_string : string -> t
val to_string : t -> string
val to_int : t -> int
val is_int : t -> bool
