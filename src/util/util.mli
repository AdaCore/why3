(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)
open Stdlib
(** Useful functions *)

val ($) : ('a -> 'b) -> 'a -> 'b

val const : 'a -> 'b -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val cons : ('a -> 'b) -> 'b list -> 'a -> 'b list

(* useful option combinators *)

val of_option : 'a option -> 'a

val default_option : 'a -> 'a option -> 'a

val option_map : ('a -> 'b) -> 'a option -> 'b option

val option_iter : ('a -> unit) -> 'a option -> unit

val option_apply : 'b -> ('a -> 'b) -> 'a option -> 'b

val option_fold : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b
(** [option_fold f d o] returns [d] if [o] is [None], and
    [f d x] if [o] is [Some x] *)

val option_eq : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool

val option_map_fold :
  ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option

(* useful list combinators *)

val rev_map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val map_join_left : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'a list -> 'b

val list_apply : ('a -> 'b list) -> 'a list -> 'b list
(** [list_apply f [a1;..;an] returns (f a1)@...@(f an) *)

val list_fold_product :
  ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  (** [list_fold_product f acc l1 l2] apply the function [f] with the
      accumulator [acc] on all the pair of elements of [l1] and [l2]
      tail-reccursive *)

val list_fold_product_l :
  ('a -> 'b list -> 'a) -> 'a -> 'b list list -> 'a
  (** generalisation of {! list_fold_product}
      not tail-reccursive *)

val list_compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

(* boolean fold accumulators *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
val any_fn : ('a -> bool) -> 'b -> 'a -> bool

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)
val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)

(* Set and Map on ints and strings *)

module Sint : Set.S with type elt = int
module Mint : Map.S with type key = int

module Sstr : Set.S with type elt = string
module Mstr : Map.S with type key = string

val memo_int : int -> (int -> 'a) -> int -> 'a

(* Set, Map, Hashtbl on structures with a unique tag *)

module type Tagged =
sig
  type t
  val tag : t -> int
end

module type OrderedHash =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHash (X : Tagged) : OrderedHash with type t = X.t
module OrderedHashList (X : Tagged) : OrderedHash with type t = X.t list

module StructMake (X : Tagged) :
sig
  module M : Map.S with type key = X.t
  module S : Map.SetS with type elt = X.t and type t = unit M.t
  module H : Hashtbl.S with type key = X.t
end

module WeakStructMake (X : Hashweak.Weakey) :
sig
  module M : Map.S with type key = X.t
  module S : Map.SetS with type elt = X.t and type t = unit M.t
  module H : Hashtbl.S with type key = X.t
  module W : Hashweak.S with type key = X.t
end

