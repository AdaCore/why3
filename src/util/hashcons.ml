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

(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t
    val hashcons : t -> t
    val iter : (t -> unit) -> unit
    val stats : unit -> int * int * int * int * int * int
  end

module Make(H : HashedType) : (S with type t = H.t) =
struct
  type t = H.t

  module WH = Weak.Make (H)

  let next_tag = ref 0

  let htable = WH.create 5003

  let hashcons d =
    let d = H.tag !next_tag d in
    let o = WH.merge htable d in
    if o == d then incr next_tag;
    o

  let iter f = WH.iter f htable

  let stats () = WH.stats htable
end

let combine acc n = n * 65599 + acc
let combine2 acc n1 n2 = combine acc (combine n1 n2)
let combine3 acc n1 n2 n3 = combine acc (combine n1 (combine n2 n3))
let combine_list f = List.fold_left (fun acc x -> combine acc (f x))
let combine_option h = function None -> 0 | Some s -> (h s) + 1
let combine_pair h1 h2 (a1,a2) = combine (h1 a1) (h2 a2)

