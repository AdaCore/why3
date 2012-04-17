(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Format
open Why3
open Ident

(* records definition locations *)

val set_loadpath: string list -> unit
val set_output_dir: string option -> unit

val output_file: string -> string

val add_file: string -> unit

val add_ident: ident -> unit

type tag = string

val is_def: string * int * int -> tag
  (* if [loc] is a definition point, returns the corresponding tag,
     otrherwise raises [Not_found] *)

val locate: ident -> string * tag
  (* or raises [Not_found] *)

