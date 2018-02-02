(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Useful list combinators *)

val rev_map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val map_fold_right :
  ('a -> 'acc -> 'b * 'acc) -> 'a list -> 'acc -> 'b list * 'acc

val map_filter : ('a -> 'b option) -> 'a list -> 'b list

val equal : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val cons : ('a -> 'b) -> 'b list -> 'a -> 'b list

val map_join_left : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'a list -> 'b

val apply : ('a -> 'b list) -> 'a list -> 'b list
(** [apply f [a1;..;an]] returns (f a1)@...@(f an) *)

val fold_product : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
(** [fold_product f acc l1 l2] apply the function [f] with the
    accumulator [acc] on all the pair of elements of [l1] and [l2]
    tail-recursive *)

val fold_product_l : ('a -> 'b list -> 'a) -> 'a -> 'b list list -> 'a
(** generalisation of {! Lists.fold_product}; not tail-recursive *)

val flatten_rev : 'a list list -> 'a list

val part : ('a -> 'a -> int) -> 'a list -> 'a list list
(** [part cmp l] returns the list of the congruence classes with
    respect to [cmp]. They are returned in reverse order *)

val first : ('a -> 'b option) -> 'a list -> 'b
(** [first f l] returns the first result of the application of
    [f] to an element of [l] which doesn't return [None]. [raise
    Not_found] if all the element of [l] return [None] *)

val find_nth : ('a -> bool) -> 'a list -> int
(** [find_nth p l] returns the index of the first element that
    satifies the predicate [p]. [raise Not_found] if no element of [l]
    verify the predicate *)

val first_nth : ('a -> 'b option) -> 'a list -> int * 'b
(** The combinaison of {!list_first} and {!list_find_nth}. *)

val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
val iteri : (int -> 'a -> unit) -> 'a list -> unit
val fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b list -> 'a
(** similar to List.map, List.iter and List.fold_left,
    but with element index passed as extra argument (in 0..len-1) *)

val prefix : int -> 'a list -> 'a list
(** the first n elements of a list *)

val chop : int -> 'a list -> 'a list
(** removes the first n elements of a list;
    raises Invalid_argument if the list is not long enough *)

val chop_last : 'a list -> 'a list * 'a
(** removes (and returns) the last element of a list *)
