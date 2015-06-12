(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Wrappers for deprecated string functions of OCaml stdlib *)

val create : int -> string
val copy : string -> string
val set : string -> int -> char -> unit

(** Useful functions on string *)

val rev_split : char -> string -> string list

val split : char -> string -> string list

val ends_with : string -> string -> bool
(** test if a string ends with another *)

val pad_right : char -> string -> int -> string
(** chop or pad the given string on the right up to the given length *)
