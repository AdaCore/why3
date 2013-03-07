(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Ident

(* records definition locations *)

val set_loadpath: string list -> unit
val set_output_dir: string option -> unit
val set_stdlib_url: string -> unit

val output_file: string -> string

val add_file: string -> unit

val add_ident: ident -> unit

type tag = string

val is_def: string * int * int -> tag
  (* if [loc] is a definition point, returns the corresponding tag,
     otrherwise raises [Not_found] *)

type url = string

val locate: ident -> string * url * tag
  (* returns (filename, url, tag) or raises [Not_found] *)

