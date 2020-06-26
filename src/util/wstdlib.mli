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

(** Specific instances of Set, Map, Hashtbl on int, string, float, and tagged types *)

module Mint : Extmap.S with type key = int
module Sint : Extset.S with module M = Mint
module Hint : Exthtbl.S with type key = int

module Mstr : Extmap.S with type key = string
module Sstr : Extset.S with module M = Mstr
module Hstr : Exthtbl.S with type key = string

module Mfloat : Extmap.S with type key = float
module Sfloat : Extset.S with module M = Mfloat
module Hfloat : Exthtbl.S with type key = float

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

module OrderedHashed (X : TaggedType) :
  OrderedHashedType with type t = X.t

module OrderedHashedList (X : TaggedType) :
  OrderedHashedType with type t = X.t list

module MakeMSH (X : TaggedType) :
sig
  module M : Extmap.S with type key = X.t
  module S : Extset.S with module M = M
  module H : Exthtbl.S with type key = X.t
end

module MakeMSHW (X : Weakhtbl.Weakey) :
sig
  module M : Extmap.S with type key = X.t
  module S : Extset.S with module M = M
  module H : Exthtbl.S with type key = X.t
  module W : Weakhtbl.S with type key = X.t
end

module Int : OrderedHashedType with type t = int
