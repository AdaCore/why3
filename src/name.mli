(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

type t
(** the type of Names *)

val from_string : string -> t
(** create a new name from a string *)

val fresh : t -> t
(** generate a new name from an old one *)

val equal : t -> t -> bool
(** efficient equality test on names *)

val compare : t -> t -> int
(** efficient comparison on names *)

val hash : t -> int
(** compute a hash for this name *)

val unsafe_to_string : t -> string
(** convert a name to a string; does not guarantee uniqueness. *)

val to_string : t -> string
(** get a unique string for a name. This name is memoized between calls,
  so that [to_string n] always returns the same string for the same name.
  Call [reset] to reset the memoization information. *)

val print : Format.formatter -> t -> unit
(** pretty printing names, using [to_string] to obtain a unique string. *)

val reset : unit -> unit
(* Reset the memoization information. Strings obtained using
   [to_string] or [print] after resetting are not guaranteed to be different
   from strings obtained before. *)

module M : Map.S with type key = t
module S : Set.S with type elt = t

(* val build_map : t list -> int M.t *)
(* (\** from the list [ [n_1; ... ; n_m] ] of names build the map *)
(*  * [ n_1 |-> 0 ; ... n_m |-> m -1 ] *\) *)
