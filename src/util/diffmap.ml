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

exception Duplicate

module type S = sig
  module M : Extmap.S
  type key = M.key
  type 'a t
  val empty: unit -> 'a t
  val create: 'a M.t -> 'a t
  val union: 'a t -> 'a M.t -> 'a t
  val get: 'a t -> 'a M.t
end

module MakeOfMap (M: Extmap.S) = struct
  module M = M
  type key = M.key

  type 'a diff =
    | Madd of 'a M.t * 'a t
    | Msub of 'a M.t * 'a t
    | Mmap of 'a M.t
  and 'a t = { mutable diff : 'a diff }

  let empty () = { diff = Mmap M.empty }

  let create m = { diff = Mmap m }

  let rec get x =
    match x.diff with
    | Madd (d,y) ->
        let my = get y in
        let mx = M.union (fun _ _ _ -> raise Duplicate) my d in
        y.diff <- Msub (d, x);
        x.diff <- Mmap mx;
        mx
    | Msub (d,y) ->
        let my = get y in
        let mx = M.set_diff my d in
        y.diff <- Madd (d, x);
        x.diff <- Mmap mx;
        mx
    | Mmap mx -> mx

  let union x d =
    if M.is_empty d then x
    else
      let mx = get x in
      let my = M.union (fun _ _ _ -> raise Duplicate) mx d in
      let y = { diff = Mmap my } in
      x.diff <- Msub (d, y);
      y
end

module type OrderedType = Map.OrderedType

module Make (Ord: OrderedType) = MakeOfMap(Extmap.Make(Ord))
