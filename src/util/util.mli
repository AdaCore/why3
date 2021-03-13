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

(** Useful functions *)

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val const3 : 'a -> 'b -> 'c -> 'd -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val foldi : ('a -> int -> 'a) -> 'a -> int -> int -> 'a

val mapi : (int -> 'a) -> int -> int -> 'a list

val iterf : (float -> unit) -> float -> float -> float -> unit
(** [iterf f min max step] *)

(** Convert fold-like functions into [for_all] and [exists] functions.
    Predicates passed to [all], [all2], and [alld] may raise FoldSkip to
    signalize [false]. Predicates passed to [any], [any2], and [anyd] may
    raise FoldSkip to signalize [true]. *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'z -> 'a -> bool
(** [all_fn pr z a] return true if [pr a] is true,
    otherwise raise FoldSkip *)

val any_fn : ('a -> bool) -> 'z -> 'a -> bool
(** [any_fn pr z a] return false if [pr a] is false,
    otherwise raise FoldSkip *)

val all2_fn : ('a -> 'b -> bool) -> 'z -> 'a -> 'b -> bool
(** [all2_fn pr z a b] return true if [pr a b] is true,
    otherwise raise FoldSkip *)

val any2_fn : ('a -> 'b -> bool) -> 'z -> 'a -> 'b -> bool
(** [any2_fn pr z a b] return false if [pr a b] is false,
    otherwise raise FoldSkip *)

type ('z,'a,'c) fold = ('z -> 'a -> 'z) -> 'z -> 'c -> 'z

val all : (bool,'a,'c) fold -> ('a -> bool) -> 'c -> bool
val any : (bool,'a,'c) fold -> ('a -> bool) -> 'c -> bool

type ('z,'a,'b,'c,'d) fold2 = ('z -> 'a -> 'b -> 'z) -> 'z -> 'c -> 'd -> 'z

val all2 : (bool,'a,'b,'c,'d) fold2 -> ('a -> 'b -> bool) -> 'c -> 'd -> bool
val any2 : (bool,'a,'b,'c,'d) fold2 -> ('a -> 'b -> bool) -> 'c -> 'd -> bool

type ('z,'a,'b,'c) foldd =
  ('z -> 'a -> 'z) -> ('z -> 'b -> 'z) -> 'z -> 'c -> 'z

val alld : (bool,'a,'b,'c) foldd -> ('a -> bool) -> ('b -> bool) -> 'c -> bool
val anyd : (bool,'a,'b,'c) foldd -> ('a -> bool) -> ('b -> bool) -> 'c -> bool

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)

val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)

(** {3 Lexical comparison using projections}

    For example to lexically sort a list [l] of pairs [(int * string) list]:

      [cmp [cmptr fst Int.compare; cmptr snd String.compare] l] *)

type 'a cmptr
(** A comparator for values of type ['a] **)

type 'a compare = 'a -> 'a -> int

val cmptr : ('a -> 'b) -> 'b compare -> 'a cmptr
(** Create a comparator by a projection and a comparison function between projected values *)

val cmptr_direct : 'a compare -> 'a cmptr

val cmp : 'a cmptr list -> 'a compare
(** Create a comparison function using lexical order defined by a list of comparators *)

val cmp_lists : 'a cmptr list -> 'a list compare
(** Create a comparison function for lists using lexical order defined by a list of comparators *)

(** {3 ANSI terminal colors} *)

val terminal_has_color : bool
(** Indicates if standard output supports ANSI terminal color codes (i.e. that the
   ["TERM"] environment variables is set, and not to ["dump"], and that standard output is
   a terminal. *)

val ansi_color_tags : Format.formatter_tag_functions
(** Functions to interpret tags as ANSI terminal color codes. The format of the tag is
   [[bold] [<color>] [on <bg-color>]].

    Possible colors are [black], [red], [green], [yellow], [blue], [magenta], [cyan], and
   [white].

    Valid formatting tags are for example ["@{<red>red text@}"], ["@{<bold>bold text@}"],
   ["@{<on green>text on green background@}"], or ["@{<bold red on green>unreadable@}"].
   *)

(** Check if a non-empty string contains only characters [a-zA-Z0-9_-] *)
val is_sexp_simple_token : string -> bool
