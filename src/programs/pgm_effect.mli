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

open Why
open Term

type reference =
  | Rlocal  of Term.vsymbol
  | Rglobal of Term.lsymbol

val name_of_reference : reference -> Ident.ident
val type_of_reference : reference -> Ty.ty
val ref_equal : reference -> reference -> bool
val reference_of_term : Term.term -> reference

module Sref : Set.S with type elt = reference
module Mref : Map.S with type key = reference

type t = private {
  reads  : Sref.t;
  writes : Sref.t;
  raises : Sls.t;
}

val empty : t

val add_read  : reference -> t -> t
val add_write : reference -> t -> t
val add_raise : lsymbol -> t -> t

val remove_reference : reference -> t -> t

val remove_raise : lsymbol -> t -> t

val union : t -> t -> t

val equal : t -> t -> bool

val no_side_effect : t -> bool

val subst : reference Mvs.t -> t -> t

val occur : reference -> t -> bool

val print_reference : Format.formatter -> reference -> unit
val print           : Format.formatter -> t         -> unit
