(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Specific instances of Set, Map, Hashtbl on int, string, float, and tagged types} *)

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

module MakeSCC (H : Exthtbl.S) :
sig
  type index
  type vertex = H.key
  type 'a source = 'a -> vertex
  type 'a visit = index -> 'a -> index
  type 'a adjacency = vertex visit -> 'a visit
  val scc : 'a source -> 'a adjacency -> 'a list -> (bool * 'a list) list
  (** [scc src adj gr] takes a directed graph [gr] represented as a list
      of adjacency descriptors of type ['a]. Each descriptor [d] in [gr]
      contains a single source vertex [src d]. The function [adj] is
      a fold-like function that takes a single-vertex visitor [fn],
      an index accumulator [k], and a descriptor [d], and traverses [d],
      applying [fn] to each vertex adjacent to [src d]. It is allowed to
      apply [fn] to vertices outside [gr], and also to apply [fn] multiple
      times to the same vertex. The result of [scc] is a list of strongly
      connected components of [gr] in a source-to-sink topological order.
      Each component is represented as a non-empty list of descriptors
      whose sources constitute the component, together with a Boolean flag
      indicating the presence of cycles inside the component. This flag
      is always true for non-singleton components. *)
end
