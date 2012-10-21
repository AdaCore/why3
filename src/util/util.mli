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

(* useful function on string *)
val split_string_rev : string -> char -> string list

val ends_with : string -> string -> bool
(** test if a string ends with another *)

val padd_string : char -> string -> int -> string
(** extract or padd the given string in order to have the given length *)

val concat_non_empty : string -> string list -> string

(* useful function on char *)
val is_uppercase : char -> bool

(* useful function on int *)
val count : int -> ('a -> int)
(** return the consecutie number from the first given *)

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

module WeakStructMake (X : Hashweak.Weakey) :
sig
  module M : Map.S with type key = X.t
  module S : M.Set
  module H : Hashtbl.S with type key = X.t
  module W : Hashweak.S with type key = X.t
end

module type PrivateHashtbl = sig
  (** Private Hashtbl *)
  type 'a t
  type key

  val find : 'a t -> key -> 'a
    (** Same as {!Hashtbl.find} *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit
    (** Same as {!Hashtbl.iter} *)
  val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
    (** Same as {!Hashtbl.fold} *)
  val mem : 'a t -> key -> bool
    (** Same as {!Hashtbl.mem} *)
  val length : 'a t -> int
    (** Same as {!Hashtbl.length} *)

end

module type PrivateArray = sig
  (** Private Array *)
  type 'a t

  val get : 'a t -> int -> 'a
  val iter : ('a -> unit) -> 'a t -> unit
    (** Same as {!Array.iter} *)
  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
    (** Same as {!Array.fold} *)

end
