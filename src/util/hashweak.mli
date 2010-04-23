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

module Make (S : Util.Tagged) : sig

  type 'a t

  val create : int -> 'a t
    (* create a hashtbl with weak keys *)

  val find : 'a t -> S.t -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> S.t -> bool
    (* test if a key is bound *)

  val add : 'a t -> S.t -> 'a -> unit
    (* bind the key with the value given *)

  val memoize : int -> (S.t -> 'a) -> (S.t -> 'a)
    (* create a memoizing function *)

  val memoize_option : int -> (S.t option -> 'a) -> (S.t option -> 'a)
    (* memoizing functions on option types *)

end
