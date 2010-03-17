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

val map_fold_left :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a list -> 'acc * 'b list

val of_option : 'a option -> 'a

val option_map : ('a -> 'b) -> 'a option -> 'b option

val option_iter : ('a -> unit) -> 'a option -> unit

val option_apply : 'b -> ('a -> 'b) -> 'a option -> 'b

exception FoldSkip

val all_fn : ('a -> bool) -> 'b -> 'a -> bool
val any_fn : ('a -> bool) -> 'b -> 'a -> bool

module Sstr : Set.S with type elt = string
module Mstr : Map.S with type key = string

