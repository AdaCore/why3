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

type node= private
  | BVar of int
  | Var of Name.t
  | Tuple of t * t
  | Arrow of t * t
and t = 
  private {tag : int ; node : node }

and scheme

val hc_equal : t -> t -> bool
val hash : t -> int

val print : Name.t list -> Format.formatter -> t -> unit

val equal : t -> t -> bool

val var : Name.t -> t
val tuple : t -> t -> t
val arrow : t -> t -> t

val instantiate_scheme : t list -> scheme -> t
val open_ : scheme -> Name.t list * t
val close : Name.t list -> t ->  scheme
val as_scheme : t -> scheme

(** internal use *)
val abstract : Name.t list -> t -> t
val instantiate : t list -> t -> t

val prop : t

val split : t -> t * t
val tuple_split : t -> t * t
