(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Useful functions on string *)

val rev_split : string -> char -> string list

val ends_with : string -> string -> bool
(** test if a string ends with another *)

val pad_right : char -> string -> int -> string
(** chop or pad the given string on the right up to the given length *)

val starts_with : string -> string -> bool
(** test if a string starts with another *)

val slice : string -> int -> int -> string
(* [slice s start end] returns the substring of s that starts at [start] and
   ends at [end-1]. Uses [String.sub] under the hood, so Invalid_argument will
   be raised if start/end do not correspond to a valid substring. *)
