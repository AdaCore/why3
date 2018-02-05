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

(* Resizable arrays *)

module RA = struct

  type 'a t = { default: 'a; mutable size: int; mutable data: 'a array }

  let length a = a.size

  let make n d = { default = d; size = n; data = Array.make n d }

  let get a i =
    if i < 0 || i >= a.size then invalid_arg "RA.get";
    a.data.(i)

  let set a i v =
    if i < 0 || i >= a.size then invalid_arg "RA.set";
    a.data.(i) <- v

  let resize a s =
    if s <= a.size then begin
      Array.fill a.data s (a.size - s) a.default
    end else begin
      let n = Array.length a.data in
      if s > n then begin
	let n' = max (2 * n) s in
	let a' = Array.make n' a.default in
	Array.blit a.data 0 a' 0 a.size;
	a.data <- a'
      end
    end;
    a.size <- s

end

(* Priority queue *)

(* The heap is encoded into a resizable array, where elements are stored
   from [0] to [length - 1]. From an element stored at [i], the left
   (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

module Make(X: Set.OrderedType) = struct
  type elt = X.t
  type t = elt RA.t
  let create ~dummy = RA.make 0 dummy
  let is_empty h = RA.length h = 0
  (* dead code
  let clear h = RA.resize h 0
  *)

  let rec move_up h x i =
    if i = 0 then RA.set h i x else
      let fi = (i - 1) / 2 in
      let y = RA.get h fi in
      if X.compare y x > 0 then begin RA.set h i y; move_up h x fi end
      else RA.set h i x

  let add h x =
    let n = RA.length h in RA.resize h (n + 1); move_up h x n

  exception Empty

  let get_min h =
    if RA.length h = 0 then raise Empty;
    RA.get h 0

  let min h l r = if X.compare (RA.get h r) (RA.get h l) < 0 then r else l

  let smallest_node h x i =
    let l = 2 * i + 1 in
    let n = RA.length h in
    if l >= n then i else
      let r = l + 1 in
      let j = if r < n then min h l r else l in
      if X.compare (RA.get h j) x < 0 then j else i

  let rec move_down h x i =
    let j = smallest_node h x i in
    if j = i then RA.set h i x
    else begin RA.set h i (RA.get h j); move_down h x j end

  let remove_min h =
    let n = RA.length h - 1 in
    if n < 0 then raise Empty;
    let x = RA.get h n in
    RA.resize h n;
    if n > 0 then move_down h x 0

  let extract_min h =
    if RA.length h = 0 then raise Empty;
    let x = RA.get h 0 in
    remove_min h;
    x

end
