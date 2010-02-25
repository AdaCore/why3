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

(** Identifiers *)

type ident = private {
  id_short : string;    (* non-unique name for string-based lookup *)
  id_long : string;     (* non-unique name for pretty printing *)
  id_origin : origin;   (* origin of the ident *)
  id_tag : int;         (* unique numeric tag *)
}

and origin =
  | User of Loc.position
  | Derived of ident
  | Fresh

module Sid : Set.S with type elt = ident
module Mid : Map.S with type key = ident
module Hid : Hashtbl.S with type key = ident

(* create a fresh ident *)
val id_fresh : string -> string -> ident

(* create a derived ident *)
val id_derive : string -> string -> ident -> ident

(* create a derived ident with the same name *)
val id_clone : ident -> ident

(* create a localized ident *)
val id_user : string -> string -> Loc.position -> ident

(** Unique persistent names for pretty printing *)

type printer

(* create new printing session *)
val create_printer : unit -> printer

(* generate a unique name for ident in the printing session *)
val id_unique : printer -> ident -> string

