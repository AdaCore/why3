(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type t
type set
val empty: set
val is_leq: set -> set -> bool
val union: t -> t -> set -> set
val join: set -> set -> set
val new_class: unit -> t
val forget: t -> set -> t option * set
val print: set -> unit
val fold_equal: ('a -> t -> t -> 'a) -> 'a -> set -> 'a
val fold_class: ('a -> t -> t -> 'a) -> 'a -> set -> 'a
val flat: set -> t list
val get_class: t -> set -> t list
val repr: t -> set -> t
val get_repr: set -> t list
