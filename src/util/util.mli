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

(* useful option combinators *)

val of_option : 'a option -> 'a

val option_map : ('a -> 'b) -> 'a option -> 'b option

val option_iter : ('a -> unit) -> 'a option -> unit

val option_apply : 'b -> ('a -> 'b) -> 'a option -> 'b

val option_eq : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool

(* useful list combinators *)

val rev_map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val list_all2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool

val map_join_left : ('a -> 'b) -> ('b -> 'b -> 'b) -> 'a list -> 'b

val list_apply : ('a -> 'b list) -> 'a list -> 'b list

val list_fold_product : 
  ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
  (** [list_fold_product f acc l1 l2] apply the function [f] with the
      accumulator [acc] on all the pair of elements of [l1] and [l2]
      tail-reccursive
  *)

val list_fold_product_l : 
  ('a -> 'b list -> 'a) -> 'a -> 'b list list -> 'a
  (** generalisation of {! list_fold_product} 
      not tail-reccursive
  *)
  
  (* boolean fold accumulators *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
val any_fn : ('a -> bool) -> 'b -> 'a -> bool

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)
val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)

(* Set and Map on strings *)

module Sstr : Set.S with type elt = string
module Mstr : Map.S with type key = string

(* Set, Map, Hashtbl on structures with a unique tag and physical equality *)
open Hashweak

module OrderedHash (X : Tagged) :
sig
  type t = X.t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

module StructMake (X : Tagged) :
sig
  module S : Set.S with type elt = X.t
  module M : Map.S with type key = X.t
  module H : Hashtbl.S with type key = X.t
  module W : Hashweak.S with type key = X.t
end

