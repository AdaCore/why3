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

(* Set, Map, Hashtbl on ints and strings *)

module Int = struct
  type t = int
  let compare (x : int) y  = Pervasives.compare x y
  let equal (x : int) y = x = y
  let hash  (x : int) = x
end

module Mint = Extmap.Make(Int)
module Sint = Extset.MakeOfMap(Mint)
module Hint = Exthtbl.Make(Int)

module Mstr = Extmap.Make(String)
module Sstr = Extset.MakeOfMap(Mstr)
module Hstr = Exthtbl.Make(struct
  type t    = String.t
  let hash  = (Hashtbl.hash : string -> int)
  let equal = ((=) : string -> string -> bool)
end)


module Float = struct
  type t = float
  let compare (x : float) y  = Pervasives.compare x y
  let equal (x : float) y = x = y
  let hash  (x : float) = Exthtbl.hash x
end

module Mfloat = Extmap.Make(Float)
module Sfloat = Extset.MakeOfMap(Mfloat)
module Hfloat = Exthtbl.Make(Float)


(* Set, Map, Hashtbl on structures with a unique tag *)

module type TaggedType =
sig
  type t
  val tag : t -> int
end

module type OrderedHashedType =
sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module OrderedHashed (X : TaggedType) =
struct
  type t = X.t
  let hash = X.tag
  let equal ts1 ts2 = X.tag ts1 == X.tag ts2
  let compare ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashedList (X : TaggedType) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = Pervasives.compare (X.tag ts1) (X.tag ts2)
  let compare = Lists.compare cmp_ts
end

module MakeMSH (X : TaggedType) =
struct
  module T = OrderedHashed(X)
  module M = Extmap.Make(T)
  module S = Extset.MakeOfMap(M)
  module H = Exthtbl.Make(T)
end

module MakeTagged (X : Weakhtbl.Weakey) =
struct
  type t = X.t
  let tag t = Weakhtbl.tag_hash (X.tag t)
end

module MakeMSHW (X : Weakhtbl.Weakey) =
struct
  module T = OrderedHashed(MakeTagged(X))
  module M = Extmap.Make(T)
  module S = Extset.MakeOfMap(M)
  module H = Exthtbl.Make(T)
  module W = Weakhtbl.Make(X)
end
