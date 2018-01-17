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

(** Sets over ordered types *)

(** Input signature of the functor {!Extset.Make}. *)
module type OrderedType = Set.OrderedType

(** Output signature of the functor {!Extset.Make}. *)
module type S =
  sig
    module M : Extmap.S
    (** The module of association tables over [elt]. *)

    type elt = M.key
    (** The type of set elements. *)

    type t = unit M.t
    (** The type of sets of type [elt]. *)

    val empty: t
    (** The empty set. *)

    val is_empty: t -> bool
    (** Test whether a set is empty or not. *)

    val mem: elt -> t -> bool
    (** [mem x s] returns [true] if [s] contains [x],
        and [false] otherwise. *)

    val add: elt -> t -> t
    (** [add x s] returns a set containing the same elements as
        [s], plus [x]. *)

    val singleton: elt -> t
    (** [singleton x] returns the one-element set that contains [x]. *)

    val remove: elt -> t -> t
    (** [remove x s] returns a set containing the same elements as [s],
        except for [x]. *)

    val merge: (elt -> bool -> bool -> bool) -> t -> t -> t
    (** [merge f s1 s2] computes a set whose elts is a subset of elts
        of [s1] and of [s2]. The presence of each such element is
        determined with the function [f]. *)

    val compare: t -> t -> int
    (** Total ordering between sets. *)

    val equal: t -> t -> bool
    (** [equal s1 s2] tests whether the sets [s1] and [s2] are equal. *)

    val subset: t -> t -> bool
    (** [subset s1 s2] tests whether the set [s1] is a subset of [s2]. *)

    val disjoint: t -> t -> bool
    (** [disjoint s1 s2] tests whether the sets [s1] and [s2]
        are disjoint. *)

    val iter: (elt -> unit) -> t -> unit
    (** [iter f s] applies [f] to all elements of [s].
        The elements are passed to [f] in increasing order with respect
        to the ordering over the type of the elts. *)

    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    (** [fold f s a] computes [(f eN ... (f e1 a)...)],
        where [e1 ... eN] are the element of [s] in increasing order. *)

    val for_all: (elt -> bool) -> t -> bool
    (** [for_all p s] checks if all the elements of [s] satisfy
        the predicate [p]. *)

    val exists: (elt -> bool) -> t -> bool
    (** [exists p s] checks if at least one element of [s] satisfies
        the predicate [p]. *)

    val filter: (elt -> bool) -> t -> t
    (** [filter p s] returns the set with all the elements of [s]
        that satisfy predicate [p]. *)

    val partition: (elt -> bool) -> t -> t * t
    (** [partition p s] returns a pair of sets [(s1, s2)], where
        [s1] contains all the elements of [s] that satisfy the
        predicate [p], and [s2] is the map with all the elements
        of [s] that do not satisfy [p]. *)

    val cardinal: t -> int
    (** Return the number of elements in a set. *)

    val elements: t -> elt list
    (** Return the list of all elements of the given set.
        The returned list is sorted in increasing order. *)

    val min_elt: t -> elt
    (** Return the smallest element of the given set or raise
        [Not_found] if the set is empty. *)

    val max_elt: t -> elt
    (** Return the largest element of the given set or raise
        [Not_found] if the set is empty. *)

    val choose: t -> elt
    (** Return one element of the given set, or raise [Not_found] if
        the set is empty. Which element is chosen is unspecified,
        but equal elements will be chosen for equal sets. *)

    val split: elt -> t -> t * bool * t
    (** [split x s] returns a triple [(l, mem, r)], where
        [l] is the set with all the elements of [s] that are
        strictly less than [x];
        [r] is the set with all the elements of [s] that are
        strictly greater than [x];
        [mem] is [true] if [x] belongs to [s] and [false] otherwise. *)

    val change : (bool -> bool) -> elt -> t -> t
    (** [change f x s] returns a set containing the same elements as
        [s], except [x] which is added to [s] if [f (mem x s)] returns
        [true] and removed otherwise. *)

    val union : t -> t -> t
    (** [union f s1 s2] computes the union of two sets *)

    val inter : t -> t -> t
    (** [inter f s1 s2] computes the intersection of two sets *)

    val diff : t -> t -> t
    (** [diff f s1 s2] computes the difference of two sets *)

    val fold_left : ('b -> elt -> 'b) -> 'b -> t -> 'b
    (** same as {!fold} but in the order of {!List.fold_left} *)

    val fold2_inter : (elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
    (** [fold2_inter f s1 s2 a] computes [(f eN ... (f e1 a) ...)],
        where [e1 ... eN] are the elements of [inter s1 s2]
        in increasing order. *)

    val fold2_union : (elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
    (** [fold2_union f s1 s2 a] computes [(f eN ... (f e1 a) ...)],
        where [e1 ... eN] are the elements of [union s1 s2]
        in increasing order. *)

    val translate : (elt -> elt) -> t -> t
    (** [translate f s] translates the elements in the set [s] by the
        function [f]. [f] must be strictly monotone on the elements of [s].
        Otherwise it raises [Invalid_arg]. *)

    val add_new : exn -> elt -> t -> t
    (** [add_new e x s] adds [x] to [s] if [s] does not contain [x],
        and raises [e] otherwise. *)

    val is_num_elt : int -> t -> bool
    (** check if the map has the given number of elements *)

    val of_list: elt list -> t
    (** construct a set from a list of elements *)

    val contains: t -> elt -> bool
    (** [contains s x] is the same as [mem x s]. *)

    val add_left: t -> elt -> t
    (** [add_left s x] is the same as [add x s]. *)

    val remove_left: t -> elt -> t
    (** [remove_left s x] is the same as [remove x s]. *)

    val print: (Format.formatter -> elt -> unit) ->
               Format.formatter -> t -> unit
  end

module MakeOfMap (M : Extmap.S) : S with module M = M
(** Functor building an implementation of the set structure
    given a totally ordered type. *)

module Make (Ord : OrderedType) : S with type M.key = Ord.t
(** Functor building an implementation of the set structure
    given a totally ordered type. *)
