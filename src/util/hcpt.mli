(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Hash-consed Patricia Trees

    Sets and maps with O(1) hash and equality.
*)

module type M = sig
  type key
  type value

  type t
  val hash : t -> int
  val equal : t -> t -> bool

  val id : t -> int
    (** unique *)

  val empty : t
  val is_empty : t -> bool
  val mem : key -> t -> bool
  val find : key -> t -> value
  val find_opt : key -> t -> value option
  val add : key -> value -> t -> t
  val singleton : key -> value -> t
  val remove : key -> t -> t
  val cardinal : t -> int
  val iter : (key -> value -> unit) -> t -> unit
  val fold : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_left : ('a -> key -> value -> 'a) -> 'a -> t -> 'a
  val fold_right : (key -> value -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (key -> value -> bool) -> t -> bool
  val exists : (key -> value -> bool) -> t -> bool
  val filter : (key -> value -> bool) -> t -> t
  val filter_map : (key -> value -> value option) -> t -> t
  val partition : (key -> value -> bool) -> t -> t * t
  val min_binding : t -> key * value
  val min_binding_opt : t -> (key * value) option
  val max_binding : t -> key * value
  val max_binding_opt : t -> (key * value) option
  val choose : t -> key * value
  val choose_opt : t -> (key * value) option
  val split : key -> t -> t * value option * t
  val keys : t -> key list
  val bindings : t -> (key * value) list
  val compare : (value -> value -> int) -> t -> t -> int
(*
  val update : key -> (value option -> value option) -> t -> t
  val merge :
    (key -> value option -> value option -> value option) ->
    t -> t -> t
  val union :
    (key -> value -> value -> value option) -> t -> t -> t
  val inter :
    (key -> value -> value -> value option) -> t -> t -> t
  val diff :
    (key -> value -> value -> value option) -> t -> t -> t
*)
  val to_seq : t -> (key * value) Seq.t
  val to_seq_from : key -> t -> (key * value) Seq.t
  val add_seq : (key * value) Seq.t -> t -> t
  val of_seq : (key * value) Seq.t -> t
end

module type S = sig
  type elt

  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val id : t -> int

  val empty : t
  val is_empty : t -> bool
  val mem : elt -> t -> bool
  val add : elt -> t -> t
  val singleton : elt -> t
  val remove : elt -> t -> t
  val cardinal : t -> int
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_left : ('a -> elt -> 'a) -> 'a -> t -> 'a
  val fold_right : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val filter : (elt -> bool) -> t -> t
  val partition : (elt -> bool) -> t -> t * t
  val min_elt : t -> elt
  val min_elt_opt : t -> elt option
  val max_elt : t -> elt
  val max_elt_opt : t -> elt option
  val choose : t -> elt
  val choose_opt : t -> elt option
  val split : elt -> t -> t * bool * t
  val elements : t -> elt list
  val compare : t -> t -> int
(*
  val merge : (elt -> bool -> bool -> bool) -> t -> t -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val disjoint : t -> t -> bool
*)
  val to_seq : t -> elt Seq.t
  val to_seq_from : elt -> t -> elt Seq.t
  val add_seq : elt Seq.t -> t -> t
  val of_seq : elt Seq.t -> t
end

module MakeMap(X : sig
  type t
  val id : t -> int
  type value
  val hash : value -> int
  val equal : value -> value -> bool
end) : M with type key = X.t and type value = X.value


module MakeSet(X : sig
  type t
  val id : t -> int
end) : S with type elt = X.t

