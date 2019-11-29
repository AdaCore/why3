(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

module type S = sig

  type key

  type 'a t

  val create : int -> 'a t
    (* create a hashtbl with weak keys *)

  val clear : 'a t -> unit

  val copy : 'a t -> 'a t

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val remove : 'a t -> key -> unit
    (* remove the value *)

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val iterk : (key -> unit) -> 'a t -> unit

  val foldk : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val length : 'a t -> int

  val memoize : int -> (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_rec : int -> ((key -> 'a) -> (key -> 'a)) -> (key -> 'a)
    (* create a memoizing recursive function *)

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

type tag = int

let create_tag tag = tag

let dummy_tag = -1

let tag_equal : tag -> tag -> bool = (==)

let tag_hash k = assert (k != dummy_tag); k

module type Weakey =
sig
  type t
  val tag : t -> tag
end

module Make (S : Weakey) : S with type key = S.t = struct

  type key = S.t

  module H = Ephemeron.K1.Make (struct
    type t = S.t
    let hash k = (S.tag k)
    let equal k1 k2 = S.tag k1 == S.tag k2
  end)

  type 'a t = 'a H.t

  let create = H.create


  let find = H.find

  let mem = H.mem

  let set = H.replace

  let remove = H.remove

  let iter = H.iter
  let fold = H.fold

  let iterk fn t = H.iter (fun k _ -> fn k) t
  let foldk fn t = H.fold (fun k _ -> fn k) t

  let clear = H.clear

  let length = H.length

  let copy = H.copy

  let memoize n fn =
    let h = create n in fun e ->
      try find h e
      with Not_found ->
        let v = fn e in
        set h e v;
        v

  let memoize_rec n fn =
    let h = create n in
    let rec f e =
      try find h e
      with Not_found ->
        let v = fn f e in
        set h e v;
        v
    in
    f

  let memoize_option n fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end
