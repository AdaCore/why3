(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

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

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

type tag = {
  tag_map : ((int,Obj.t) Hashtbl.t) Lazy.t;
  tag_tag : int;
}

let create_tag tag = {
  tag_map = lazy (Hashtbl.create 3);
  tag_tag = tag;
}

let dummy_tag = {
  tag_map = lazy (failwith "dummy tag");
  tag_tag = -1;
}

let tag_equal = (==)

let tag_hash k = assert (k != dummy_tag); k.tag_tag

module type Weakey =
sig
  type t
  val tag : t -> tag
end

module Make (S : Weakey) = struct

  type key = S.t

  module H = Weak.Make (struct
    type t = S.t
    let hash k = (S.tag k).tag_tag
    let equal k1 k2 = S.tag k1 == S.tag k2
  end)

  type 'a t = {
    tbl_set : H.t;
    tbl_tag : int;
  }

  let tag_map k = Lazy.force (S.tag k).tag_map

  let find (t : 'a t) k : 'a =
    Obj.obj (Hashtbl.find (tag_map k) t.tbl_tag)

  let mem t k = Hashtbl.mem (tag_map k) t.tbl_tag

  let set (t : 'a t) k (v : 'a) =
    Hashtbl.replace (tag_map k) t.tbl_tag (Obj.repr v);
    H.add t.tbl_set k

  let remove t k =
    Hashtbl.remove (tag_map k) t.tbl_tag;
    H.remove t.tbl_set k

  let iterk fn t = H.iter fn t.tbl_set
  let foldk fn t = H.fold fn t.tbl_set

  let iter  fn t = H.iter (fun k -> fn k (find t k)) t.tbl_set
  let fold  fn t = H.fold (fun k -> fn k (find t k)) t.tbl_set

  let tbl_final t = iterk (fun k -> Hashtbl.remove (tag_map k) t.tbl_tag) t

  let create = let c = ref (-1) in fun n ->
    let t = {
      tbl_set = H.create n;
      tbl_tag = (incr c; !c) }
    in
    Gc.finalise tbl_final t;
    t

  let clear t = tbl_final t; H.clear t.tbl_set

  let length t = H.count t.tbl_set

  let copy t =
    let t' = create (length t) in
    iter (set t') t;
    t'

  let memoize n fn =
    let h = create n in fun e ->
      try find h e
      with Not_found ->
        let v = fn e in
        set h e v;
        v

  let memoize_option n fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end

