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

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val of_option : 'a option -> 'a

val option_map : ('a -> 'b) -> 'a option -> 'b option

val option_iter : ('a -> unit) -> 'a option -> unit

val option_apply : 'b -> ('a -> 'b) -> 'a option -> 'b

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
val any_fn : ('a -> bool) -> 'b -> 'a -> bool

module Sstr : Set.S with type elt = string
module Mstr : Map.S with type key = string

module type Sstruct =
sig
  type t
  val tag : t -> int
end

module OrderedHash (X:Sstruct) :
sig
  type t = X.t
  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end


(* Use physical equality on X.t *)
module StructMake(X : Sstruct) :
sig
  module S : Set.S with type elt = X.t
  module M : Map.S with type key = X.t
  module H : Hashtbl.S with type key = X.t
end
