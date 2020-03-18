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

module type S =
sig
  include Hashtbl.S
  val find_def : 'a t -> 'a -> key -> 'a
  val find_opt : 'a t -> key -> 'a option
  val find_exn : 'a t -> exn -> key -> 'a
  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  val memo : int -> (key -> 'a) -> key -> 'a
  val is_empty : 'a t -> bool
end

module type Private =
sig
  type 'a t
  type key
  val find : 'a t -> key -> 'a
  val find_def : 'a t -> 'a -> key -> 'a
  val find_opt : 'a t -> key -> 'a option
  val find_exn : 'a t -> exn -> key -> 'a
  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
  val mem : 'a t -> key -> bool
  val length : 'a t -> int
  val is_empty : 'a t -> bool
end

let hash = Hashtbl.hash

module Make (X:Hashtbl.HashedType) : S with type key = X.t =
struct
  module M = Hashtbl.Make(X)
  include M

  let memo size f =
    let h = create size in
    fun x -> try find h x
      with Not_found -> let y = f x in add h x y; y

  let find_def h d k =
    try find h k with Not_found -> d

  let find_exn h e k =
    try find h k with Not_found -> raise e

  let find_opt h k =
    try Some (find h k) with Not_found -> None

  let map f h =
    let h' = create (length h) in
    iter (fun k x -> add h' k (f k x)) h;
    h'

  let is_empty h = length h = 0
end
