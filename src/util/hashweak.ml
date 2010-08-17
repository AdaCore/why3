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

module Weak : sig

  type key

  type 'a t

  val create_key : unit -> key

  val create : unit -> 'a t
    (* create a hashtbl with weak keys *)

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

end = struct

  type key = ((int,Obj.t) Hashtbl.t) Lazy.t

  type 'a t = int

  let create_key () = lazy (Hashtbl.create 3)

  let create = let c = ref (-1) in fun () -> incr c; !c

  let find t k  = Obj.obj (Hashtbl.find (Lazy.force k) t)
  let mem t k   = Hashtbl.mem (Lazy.force k) t
  let set t k v = Hashtbl.replace (Lazy.force k) t (Obj.repr v)

end

include Weak

module type S = sig

  type key

  type 'a t

  val create : unit -> 'a t
    (* create a hashtbl with weak keys *)

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val memoize : (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_option : (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

module type Weakey =
sig
  type t
  val key : t -> Weak.key
end

module Make (S : Weakey) = struct

  type key = S.t

  type 'a t = 'a Weak.t

  let create = Weak.create

  let set_key  h = Weak.set  h
  let mem_key  h = Weak.mem  h
  let find_key h = Weak.find h

  let set_key h k v =
    assert (not (mem_key h k));
    set_key h k v

  let set  h e = set_key  h (S.key e)
  let mem  h e = mem_key  h (S.key e)
  let find h e = find_key h (S.key e)

  let memoize fn =
    let h = create () in fun e ->
      let k = S.key e in
      try find_key h k
      with Not_found ->
        let v = fn e in
        set_key h k v;
        v

  let memoize_option fn =
    let v = lazy (fn None) in
    let fn e = fn (Some e) in
    let fn = memoize fn in
    function
      | Some e -> fn e
      | None -> Lazy.force v

end

