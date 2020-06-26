(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

exception Duplicate

(** Input signature of the functor {!Diffmap.Make}. *)
module type OrderedType = Map.OrderedType

(** Output signature of the functor {!Diffmap.Make}. *)
module type S = sig
  module M : Extmap.S

  type key = M.key
  (** The type of the map keys. *)

  type 'a t
  (** The type of maps from type [key] to type ['a]. *)

  val empty: unit -> 'a t
  (** [empty ()] creates an empty map. *)

  val create: 'a M.t -> 'a t
  (** [create m] creates a map initialized with [m] *)

  val union: 'a t -> 'a M.t -> 'a t
  (** [union m d] behaves as [create (M.union ... (get m) d)].
      The new map, however, shares the content of [m], so the memory
      consumption increases only by [O(#d)] rather than [O(#m + #d)].
      The function raises [Duplicate] if [m] and [d] contains the same key. *)

  val get: 'a t -> 'a M.t
  (** [get m] returns the content of [m].
      When called twice in a row on [m], the second call is constant time.
      When {!Diffmap.S.union} and [get] are called in a tree-traversal
      fashion, e.g., by a backtracking algorithm, the calls to [get] are
      amortized constant time. *)

end

module MakeOfMap (M : Extmap.S): S with module M = M
(** Functor building an implementation of the map structure
    given a map type. *)

module Make (Ord: OrderedType): S with type M.key = Ord.t
(** Functor building an implementation of the map structure
    given a totally ordered type. *)
