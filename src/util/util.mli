(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib

(** Useful functions *)

val ($) : ('a -> 'b) -> 'a -> 'b
val (|>) : 'a -> ('a -> 'b) -> 'b

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val const3 : 'a -> 'b -> 'c -> 'd -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

(* useful int iterator *)
val foldi : ('a -> int -> 'a) -> 'a -> int -> int -> 'a
val mapi : (int -> 'a) -> int -> int -> 'a list

(* useful float iterator *)
val iterf : (float -> unit) -> float -> float -> float -> unit
(** [iterf f min max step] *)

(* boolean fold accumulators *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
(* [all_fn pr b a] return true if pr is true on a, otherwise raise FoldSkip *)
val any_fn : ('a -> bool) -> 'b -> 'a -> bool
(* [all_fn pr b a] return false if pr is false on a,
   otherwise raise FoldSkip *)

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)

val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)

(* Set and Map on ints and strings *)

module Mint : Map.S with type key = int
module Sint : Mint.Set
module Hint : Hashtbl.S with type key = int

module Mstr : Map.S with type key = string
module Sstr : Mstr.Set
module Hstr : Hashtbl.S with type key = string

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
  module S : M.Set
  module H : Hashtbl.S with type key = X.t
end

module WeakStructMake (X : Weakhtbl.Weakey) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Hashtbl.S with type key = X.t
  module W : Weakhtbl.S with type key = X.t
end
