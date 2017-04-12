(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

val lowercase : string -> string
val capitalize : string -> string
val uncapitalize : string -> string

(** {2 Other useful functions on strings} *)

val rev_split : char -> string -> string list

val split : char -> string -> string list
(** [split c s] splits [s] into substrings, taking as delimiter the
    character [c], and returns the list of substrings.  An occurrence of
    the delimiter at the beginning or at the end of the string is
    ignored. *)

val bounded_split : char -> string -> int -> string list
(** [bounded_split c s n] do the same as [split c s] but splits into
    [n] substring at most.
    The concatenation of returned substrings is equal to the string s.*)

val join : string -> string list -> string
(** [join sep l] joins all the strings in [l] together, in the same
    order, separating them by [sep] *)

val ends_with : string -> string -> bool
(** test if a string ends with another *)

val pad_right : char -> string -> int -> string
(** chop or pad the given string on the right up to the given length *)

val has_prefix : string -> string -> bool
(** [has_prefix pref s] returns true if s [s] starts with prefix [pref] *)

val remove_prefix : string -> string -> string
(** [remove_prefix pref s] removes the prefix [pref] from [s]. Raises
    [Not_found] if [s] does not start with [pref] *)
