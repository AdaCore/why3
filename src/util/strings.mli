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

(** {1 Additional Useful Functions on Character Strings} *)

(** {2 Wrappers for deprecated string functions of OCaml stdlib} *)

val create : int -> string
val copy : string -> string
val set : string -> int -> char -> unit

(** {2 Other useful functions on strings} *)

val rev_split : char -> string -> string list

val split : char -> string -> string list

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
