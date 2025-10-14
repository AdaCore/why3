(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2025 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

(** {1 Utility Functions on Character Strings} *)

(** {2 Wrappers for deprecated string functions of OCaml stdlib} *)

val lowercase : string -> string
val uppercase : string -> string
val capitalize : string -> string
val uncapitalize : string -> string

(** {2 Other useful functions on strings} *)

val char_is_uppercase : char -> bool

val rev_split : char -> string -> string list

val split : char -> string -> string list
(** [split c s] splits [s] into substrings, taking as delimiter the
    character [c], and returns the list of substrings.  An occurrence of
    the delimiter at the beginning or at the end of the string is
    ignored. *)

val bounded_split : char -> string -> int -> string list
(** [bounded_split c s n] do the same as [split c s] but splits into
    [n] substring at most.
    The concatenation of returned substrings is equal to the string [s].*)

val join : string -> string list -> string
(** [join sep l] joins all the strings in [l] together, in the same
    order, separating them by [sep]. *)

val pad_right : char -> string -> int -> string
(** Chop or pad the given string on the right up to the given length. *)

val has_prefix : prefix:string -> string -> bool
(** [has_prefix prefix s] returns true if [s] starts with prefix [prefix]. *)

val remove_prefix : prefix:string -> string -> string
(** [remove_prefix pref s] removes the prefix [pref] from [s].
    @raise Not_found if [s] does not start with [pref]. *)

val has_suffix : suffix:string -> string -> bool
(** [has_suffix suffix s] returns true if [s] ends with suffix [suffix]. *)

val remove_suffix : suffix:string -> string -> string
(** [remove_suffix suff s] removes the suffix [suff] from [s].
    @raise Not_found if [s] does not end with [suff]. *)
