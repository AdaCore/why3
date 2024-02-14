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

(* Set, Map, Hashtbl on ints and strings *)

module Int = struct
  type t = int
  let compare (x : int) y = Stdlib.compare x y
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
  let compare (x : float) y = Stdlib.compare x y
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
  let compare ts1 ts2 = Int.compare (X.tag ts1) (X.tag ts2)
end

module OrderedHashedList (X : TaggedType) =
struct
  type t = X.t list
  let hash = Hashcons.combine_list X.tag 3
  let equ_ts ts1 ts2 = X.tag ts1 == X.tag ts2
  let equal = Lists.equal equ_ts
  let cmp_ts ts1 ts2 = Int.compare (X.tag ts1) (X.tag ts2)
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

module MakeSCC (H : Exthtbl.S) =
struct
  type index = int
  type vertex = H.key
  type 'a source = 'a -> vertex
  type 'a visit = index -> 'a -> index
  type 'a adjacency = vertex visit -> 'a visit

  type 'a store = {
    mutable index : int;
    element : 'a;
  }

  let scc source adjacency el =
    let ht = H.create 7 in
    let init e = H.add ht (source e) {index = 0; element = e} in
    List.iter init el;

    let tick = ref 0 in
    let sccl = ref [] in
    let path = Stack.create () in

    let mark st =
      tick := !tick + 2;
      st.index <- !tick;
      !tick in

    let pop_single v =
      H.remove ht v;
      sccl := (false, [Stack.pop path]) :: !sccl in

    let rec pop_group v scc =
      let e = Stack.pop path in
      let scc = e :: scc in
      let w = source e in
      H.remove ht w;
      if w = v then scc else pop_group v scc in

    let pop_group v =
      sccl := (true, pop_group v []) :: !sccl in

    let rec visit o v = match H.find ht v with
      | {index = 0; element = e} as st ->
          Stack.push e path;
          let i = mark st in
          let j = adjacency visit (i + 1) e in
          if j = i + 1 then pop_single v else
          if j = i then pop_group v;
          Stdlib.min o j
      | st -> Stdlib.min o st.index
      | exception Not_found -> o in

    let visit e = ignore (visit 0 (source e)) in
    List.iter visit el;
    !sccl
end
