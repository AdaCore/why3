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

open Stdlib

(** Identifiers *)

(** {2 Labels} *)

type label = string * Loc.position option

val label : ?loc:Loc.position -> string -> label

(** {2 Identifiers} *)

type ident = private {
  id_string : string;       (* non-unique name *)
  id_origin : origin;       (* origin of the ident *)
  id_label  : label list;   (* identifier labels *)
  id_tag    : Hashweak.tag; (* unique magical tag *)
}

and origin =
  | User of Loc.position
  | Derived of ident
  | Fresh

module Mid : Map.S with type key = ident
module Sid : Mid.SetS
module Hid : Hashtbl.S with type key = ident

val id_equal : ident -> ident -> bool

val id_hash : ident -> int

(* a user-created type of unregistered identifiers *)
type preid

(* register a pre-ident (never use this function) *)
val id_register : preid -> ident

(* create a fresh pre-ident *)
val id_fresh : ?labels:(label list) -> string -> preid

(* create a localized pre-ident *)
val id_user : ?labels:(label list) -> string -> Loc.position -> preid

(* create a derived pre-ident *)
val id_derive : ?labels:(label list) -> string -> ident -> preid

(* create a derived pre-ident with the same name and labels *)
val id_clone : ?labels:(label list) -> ident -> preid

(* create a duplicate pre-ident *)
val id_dup : ?labels:(label list) -> ident -> preid

(* id_derived_from i1 i2 <=> i1 is derived from i2 *)
val id_derived_from : ident -> ident -> bool

(* id_derived_from i1 i2 <=> i1 is derived from i2 *)
val id_from_user : ident -> Loc.position option

(** Unique persistent names for pretty printing *)

type ident_printer

val create_ident_printer :
  ?sanitizer : (string -> string) -> string list -> ident_printer
(** start a new printer with a sanitizing function and a blacklist *)

val id_unique :
  ident_printer -> ?sanitizer : (string -> string) -> ident -> string
(** use ident_printer to generate a unique name for ident
    an optional sanitizer is applied over the printer's sanitizer *)

val string_unique : ident_printer -> string -> string
(** Uniquify string *)

val forget_id : ident_printer -> ident -> unit
(** forget an ident *)

val forget_all : ident_printer -> unit
(** forget all idents *)

val sanitizer : (char -> string) -> (char -> string) -> string -> string
(** generic sanitizer taking a separate encoder for the first letter *)

(** various character encoders *)

val char_to_alpha : char -> string
val char_to_lalpha : char -> string
val char_to_ualpha : char -> string
val char_to_alnum : char -> string
val char_to_alnumus : char -> string

