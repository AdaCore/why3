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

(** Hashtable with weak key used for memoization *)

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
  (* assign the key to the given value *)

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
  val key : t -> key
end

module Make (S : Weakey) : S with type key = S.t

