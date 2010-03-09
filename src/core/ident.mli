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

(* a user-created type of unregistered identifiers *)
type preid

(* register a pre-ident (never use this function) *)
val id_register : preid -> ident

(* create a fresh pre-ident *)
val id_fresh : string -> preid
val id_fresh_long : string -> string -> preid

(* create a localized pre-ident *)
val id_user : string -> Loc.position -> preid
val id_user_long : string -> string -> Loc.position -> preid

(* create a derived pre-ident *)
val id_derive : string -> ident -> preid
val id_derive_long : string -> string -> ident -> preid

(* create a derived pre-ident with the same name *)
val id_clone : ident -> preid

(* create a duplicate pre-ident *)
val id_dup : ident -> preid

(** Unique persistent names for pretty printing *)

type ident_printer

(* start a new printer with a sanitizing function and a blacklist *)
val create_ident_printer :
  ?sanitizer : (string -> string) -> string list -> ident_printer

(* use ident_printer to generate a unique name for ident *)
(* an optional sanitizer is applied over the printer's sanitizer *)
val id_unique :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string

(* forget an ident *)
val forget_id : ident_printer -> ident -> unit

(* generic sanitizer taking a separate encoder for the first letter *)
val sanitizer : (char -> string) -> (char -> string) -> string -> string

(* various character encoders *)
val char_to_alpha : char -> string
val char_to_lalpha : char -> string
val char_to_ualpha : char -> string
val char_to_alnum : char -> string
val char_to_alnumus : char -> string

