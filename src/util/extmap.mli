(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* This file originates from the OCaml v 3.12 Standard Library.
   It was extended and modified for the needs of the Why3 project.
   It is distributed under the terms of its initial license, which
   is provided in the file OCAML-LICENSE. *)

(** Association tables over ordered types

   This module implements applicative association tables, also known as
   finite maps or dictionaries, given a total ordering function
   over the keys.
   All operations over maps are purely applicative (no side-effects).
   The implementation uses balanced binary trees, and therefore searching
   and insertion take time logarithmic in the size of the map.
*)

(** Input signature of the functor {!Extmap.Make}. *)
module type OrderedType = Map.OrderedType

(** Output signature of the functor {!Extmap.Make}. *)
module type S =
  sig
    type key
    (** The type of the map keys. *)

    type (+'a) t
    (** The type of maps from type [key] to type ['a]. *)

    val empty: 'a t
    (** The empty map. *)

    val is_empty: 'a t -> bool
    (** Test whether a map is empty or not. *)

    val mem: key -> 'a t -> bool
    (** [mem x m] returns [true] if [m] contains a binding for [x],
        and [false] otherwise. *)

    val add: key -> 'a -> 'a t -> 'a t
    (** [add x y m] returns a map containing the same bindings as
        [m], plus a binding of [x] to [y]. If [x] was already bound
        in [m], its previous binding disappears. *)

    val singleton: key -> 'a -> 'a t
    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x]. *)

    val remove: key -> 'a t -> 'a t
    (** [remove x m] returns a map containing the same bindings as
        [m], except for [x] which is unbound in the returned map. *)

    val merge:
         (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    (** [merge f m1 m2] computes a map whose keys is a subset of keys of [m1]
        and of [m2]. The presence of each such binding, and the corresponding
        value, is determined with the function [f]. *)

    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    (** [union f m1 m2] computes a map whose keys is a subset of keys
        of [m1] and of [m2]. If a binding is present in [m1] (resp. [m2])
        and not in [m2] (resp. [m1]) the same binding is present in
        the result. The function [f] is called only in ambiguous cases. *)

    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    (** Total ordering between maps.  The first argument is a total ordering
        used to compare data associated with equal keys in the two maps. *)

    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are
        equal, that is, contain equal keys and associate them with
        equal data.  [cmp] is the equality predicate used to compare
        the data associated with the keys. *)

    val iter: (key -> 'a -> unit) -> 'a t -> unit
    (** [iter f m] applies [f] to all bindings in map [m].
       [f] receives the key as first argument, and the associated value
       as second argument.  The bindings are passed to [f] in increasing
       order with respect to the ordering over the type of the keys. *)

    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)], where
        [k1 ... kN] are the keys of all bindings in [m] (in increasing
        order), and [d1 ... dN] are the associated data. *)

    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    (** [for_all p m] checks if all the bindings of the map
        satisfy the predicate [p]. *)

    val exists: (key -> 'a -> bool) -> 'a t -> bool
    (** [exists p m] checks if at least one binding of the map
        satisfy the predicate [p]. *)

    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    (** [filter p m] returns the map with all the bindings in [m]
        that satisfy predicate [p]. *)

    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    (** [partition p m] returns a pair of maps [(m1, m2)], where
        [m1] contains all the bindings of [s] that satisfy the
        predicate [p], and [m2] is the map with all the bindings of
        [s] that do not satisfy [p]. *)

    val cardinal: 'a t -> int
    (** Return the number of bindings of a map. *)

    val bindings: 'a t -> (key * 'a) list
    (** Return the list of all bindings of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare], where [Ord] is the argument
        given to {!Extmap.Make}. *)

    val min_binding: 'a t -> (key * 'a)
    (** Return the smallest binding of the given map
        (with respect to the [Ord.compare] ordering), or raise
        [Not_found] if the map is empty. *)

    val max_binding: 'a t -> (key * 'a)
    (** Same as {!Extmap.S.min_binding}, but returns the largest
        binding of the given map. *)

    val choose: 'a t -> (key * 'a)
    (** Return one binding of the given map, or raise [Not_found] if
        the map is empty. Which binding is chosen is unspecified,
        but equal bindings will be chosen for equal maps. *)

    val split: key -> 'a t -> 'a t * 'a option * 'a t
    (** [split x m] returns a triple [(l, data, r)], where
          [l] is the map with all the bindings of [m] whose key
        is strictly less than [x];
          [r] is the map with all the bindings of [m] whose key
        is strictly greater than [x];
          [data] is [None] if [m] contains no binding for [x],
          or [Some v] if [m] binds [v] to [x]. *)

    val find: key -> 'a t -> 'a
    (** [find x m] returns the current binding of [x] in [m],
        or raises [Not_found] if no such binding exists. *)

    val map: ('a -> 'b) -> 'a t -> 'b t
    (** [map f m] returns a map with same domain as [m], where
        the associated value [a] of all bindings of [m] has been
        replaced by the result of the application of [f] to [a].
        The bindings are passed to [f] in increasing order
        with respect to the ordering over the type of the keys. *)

    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    (** Same as {!Extmap.S.map}, but the function receives as arguments both
        the key and the associated value for each binding of the map. *)

    (** @Added in Why3 *)

    val change : ('a option -> 'a option) -> key -> 'a t -> 'a t
    (** [change f x m] returns a map containing the same bindings as
        [m], except the binding of [x] in [m] is changed from [y] to
        [f (Some y)] if [m] contains a binding of [x], otherwise the
        binding of [x] becomes [f None].

        [change f x m] corresponds to a more efficient way to do
        [match (try f (Some (find x m)) with Not_found -> f None) with
          | None -> m
          | Some v -> add x v] *)

    val inter : (key -> 'a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t
    (** [inter f m1 m2] computes a map whose keys is a subset of
        the intersection of keys of [m1] and of [m2]. *)

    val diff : (key -> 'a -> 'b -> 'a option) -> 'a t -> 'b t -> 'a t
    (** [diff f m1 m2] computes a map whose keys is a subset of keys
        of [m1]. [f] is applied on key which belongs to [m1] and [m2]
        if [f] returns [None] the binding is removed from [m1],
        otherwise [Some d1] is returned, the key binds to [d1] in [m1] *)

    val submap : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
    (** [submap pr m1 m2] verifies that all the keys in m1 are in m2
        and that for each such binding pr is verified. *)

    val disjoint : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
    (** [disjoint pr m1 m2] verifies that for every common key in m1
        and m2, pr is verified. *)

    val set_union : 'a t -> 'a t -> 'a t
    (** [set_union = union (fun _ x _ -> Some x)] *)

    val set_inter : 'a t -> 'b t -> 'a t
    (** [set_inter = inter (fun _ x _ -> Some x)] *)

    val set_diff : 'a t -> 'b t -> 'a t
    (** [set_diff = diff (fun _ _ _ -> None)] *)

    val set_submap : 'a t -> 'b t -> bool
    (** [set_submap = submap (fun _ _ _ -> true)] *)

    val set_disjoint : 'a t -> 'b t -> bool
    (** [set_disjoint = disjoint (fun _ _ _ -> false)] *)

    val set_compare : 'a t -> 'b t -> int
    (** [set_compare = compare (fun _ _ -> 0)] *)

    val set_equal : 'a t -> 'b t -> bool
    (** [set_equal = equal (fun _ _ -> true)] *)

    val find_def : 'a -> key -> 'a t -> 'a
    (** [find_def x d m] returns the current binding of [x] in [m],
        or return [d] if no such binding exists. *)

    val find_opt : key -> 'a t -> 'a option
    (** [find_opt x m] returns the [Some] of the current binding
        of [x] in [m], or return [None] if no such binding exists. *)

    val find_exn : exn -> key -> 'a t -> 'a
    (** [find_exn exn x d m] returns the current binding
        of [x] in [m], or raise [exn] if no such binding exists. *)

    val map_filter: ('a -> 'b option) -> 'a t -> 'b t
    (** Same as {!Extmap.S.map}, but may remove bindings. *)

    val mapi_filter: (key -> 'a -> 'b option) -> 'a t -> 'b t
    (** Same as {!Extmap.S.mapi}, but may remove bindings. *)

    val mapi_fold:
      (key -> 'a -> 'acc -> 'acc * 'b) -> 'a t -> 'acc -> 'acc * 'b t
    (** fold and map at the same time *)

    val mapi_filter_fold:
      (key -> 'a -> 'acc -> 'acc * 'b option) -> 'a t -> 'acc -> 'acc * 'b t
    (** Same as {!Extmap.S.mapi_fold}, but may remove bindings. *)

    val fold_left: ('b -> key -> 'a -> 'b) -> 'b -> 'a t -> 'b
    (** same as {!fold} but in the order of {!List.fold_left} *)

    val fold2_inter: (key -> 'a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
    (** fold the common keys of two map at the same time *)

    val fold2_union:
      (key -> 'a option -> 'b option -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
    (** fold the keys which appear in one of the two maps *)

    val translate : (key -> key) -> 'a t -> 'a t
    (** [translate f m] translates the keys in the map [m] by the
        function [f]. [f] must be strictly monotone on the key of [m].
        Otherwise it raises invalid_arg *)

    val add_new : exn -> key -> 'a -> 'a t -> 'a t
    (** [add_new e x v m] binds [x] to [v] in [m] if [x] is not bound,
        and raises [e] otherwise. *)

    val replace : exn -> key -> 'a -> 'a t -> 'a t
    (** [replace e x v m] binds [x] to [v] in [m] if [x] is already bound,
        and raises [e] otherwise. *)

    val keys: 'a t -> key list
    (** Return the list of all keys of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare], where [Ord] is the argument
        given to {!Extmap.Make}. *)

    val values: 'a t -> 'a list
    (** Return the list of all values of the given map.
        The returned list is sorted in increasing order with respect
        to the ordering [Ord.compare] of the keys, where [Ord] is the argument
        given to {!Extmap.Make}. *)

    val of_list: (key * 'a) list -> 'a t
    (** construct a map from a list of bindings. *)

    val contains: 'a t -> key -> bool
    (** [contains m x] is the same as [mem x m]. *)

    val domain : 'a t -> unit t
    (** [domain m] returns the set of keys of bindings in [m] *)

    val subdomain : (key -> 'a -> bool) -> 'a t -> unit t
    (** [subdomain pr m] returns the set of keys of bindings in [m]
        that satisfy predicate [pr] *)

    val is_num_elt : int -> 'a t -> bool
    (** check if the map has the given number of elements *)

    type 'a enumeration
    (** enumeration: zipper style *)

    val val_enum : 'a enumeration -> (key * 'a) option
    (** get the current key value pair of the enumeration, return None
        if the enumeration reach the end *)

    val start_enum : 'a t -> 'a enumeration
    (** start the enumeration of the given map *)

    val next_enum : 'a enumeration -> 'a enumeration
    (** get the next step of the enumeration *)

    val start_ge_enum : key -> 'a t -> 'a enumeration
    (** start the enumeration of the given map at the first key which
        is greater or equal than the given one *)

    val next_ge_enum : key -> 'a enumeration -> 'a enumeration
    (** get the next (or same) step of the enumeration which key is
        greater or equal to the given key *)
  end

module Make (Ord : OrderedType) : S with type key = Ord.t
(** Functor building an implementation of the map structure
    given a totally ordered type. *)
