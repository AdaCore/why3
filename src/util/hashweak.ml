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

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val memoize : int -> (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

module type Tagged =
sig
  type t
  val tag : t -> int
end

module Make (S : Tagged) = struct
  type key = S.t

  type 'a t = {
    table : (int,'a) Hashtbl.t;
    final : S.t -> unit;
  }

  let create n =
    let table = Hashtbl.create n in
    let w = Weak.create 1 in
    Weak.set w 0 (Some table);
    let final x = match Weak.get w 0 with
      | Some h -> Hashtbl.remove h (S.tag x)
      | None -> ()
    in
    { table = table; final = final }

  let add_tag  h = Hashtbl.add  h.table
  let mem_tag  h = Hashtbl.mem  h.table
  let find_tag h = Hashtbl.find h.table

  let set_tag h t e v =
    assert (not (mem_tag h t));
    Gc.finalise h.final e;
    add_tag h t v

  let set  h e = set_tag  h (S.tag e) e
  let mem  h e = mem_tag  h (S.tag e)
  let find h e = find_tag h (S.tag e)

  let memoize n fn =
    let h = create n in fun e ->
      let t = S.tag e in
      try find_tag h t
      with Not_found ->
        let v = fn e in
        set_tag h t e v;
        v

  let memoize_option n fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in 
    let fn = memoize n fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end

