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

(* useful combinators *)

let ($) f x = f x
let (|>) x f = f x

let const f _ = f

let const2 f _ _ = f

let const3 f _ _ _ = f

let flip f x y = f y x

(* useful iterator on int *)
let rec foldi f acc min max =
  if min > max then acc else foldi f (f acc min) (succ min) max
let mapi f = foldi (fun acc i -> f i::acc) []

(* useful iterator on float *)
let rec iterf f min max step =
  if min > max then () else
    (f min; iterf f (min+.step) max step)

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr _ t = pr t || raise FoldSkip
let any_fn pr _ t = pr t && raise FoldSkip

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

(* Set and Map on ints and strings *)

module Int  = struct
  type t = int
  let compare = Pervasives.compare
  let equal x y = x = y
  let hash x = x
 end

module Mint = Map.Make(Int)
module Sint = Mint.Set
module Hint = Hashtbl.Make(Int)

module Mstr = Map.Make(String)
module Sstr = Mstr.Set
module Hstr = Hashtbl.Make
  (struct
    type t = String.t
    let hash    = (Hashtbl.hash : string -> int)
    let equal   = ((=) : string -> string -> bool)
  end)

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

module OrderedHash (X : Tagged) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashList (X : Tagged) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
  let compare = Lists.compare cmp_ts
end

module StructMake (X : Tagged) =
struct
  module T = OrderedHash(X)
  module M = Map.Make(T)
  module S = M.Set
  module H = Hashtbl.Make(T)
end

module MakeTagged (X : Weakhtbl.Weakey) =
struct
  type t = X.t
  let tag t = Weakhtbl.tag_hash (X.tag t)
end

module WeakStructMake (X : Weakhtbl.Weakey) =
struct
  module T = OrderedHash(MakeTagged(X))
  module M = Map.Make(T)
  module S = M.Set
  module H = Hashtbl.Make(T)
  module W = Weakhtbl.Make(X)
end

module type PrivateHashtbl = sig
  (** Private Hashtbl *)
  type 'a t
  type key

  val find : 'a t -> key -> 'a
    (** Same as {Hashtbl.find} *)
  val iter : (key -> 'a -> unit) -> 'a t -> unit
    (** Same as {Hashtbl.iter} *)
  val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
    (** Same as {Hashtbl.fold} *)
  val mem : 'a t -> key -> bool
    (** Same as {Hashtbl.mem} *)
  val length : 'a t -> int
    (** Same as {Hashtbl.length} *)

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
