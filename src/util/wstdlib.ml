(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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

let fold_of_iter iter f k e =
  let r = ref k in iter (fun v -> r := f !r v) e; !r

module MakeSCC (H : Exthtbl.S) =
struct
  type vertex = H.key
  type 'a source = 'a -> vertex
  type 'a adjacency = (vertex -> unit) -> 'a -> unit
  type 'a register = { elt: 'a; mutable index: int }

  let scc source adjacency el =
    let st = Stack.create () in
    let ht = H.create 7 in
    let cl = ref [] in

    let rec evict n scc =
      let e = Stack.pop st in
      let scc = e :: scc in
      H.remove ht (source e);
      if n = 0 then scc else
        evict (n - 1) scc in

    let evict i = evict (Stack.length st - i) [] in

    let rec visit o v = match H.find ht v with
      | {elt = e; index = 0} as r ->
          Stack.push e st;
          let i = r.index <- Stack.length st; r.index in
          let j = fold_of_iter adjacency visit (i + 1) e in
          if j >= i then cl := (j = i, evict i) :: !cl;
          Stdlib.min o j
      | r -> Stdlib.min o r.index
      | exception Not_found -> o in

    List.iter (fun e -> H.add ht (source e) {elt = e; index = 0}) el;
    List.iter (fun e -> ignore (visit 0 (source e))) el;
    !cl
end
