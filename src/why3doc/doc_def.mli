(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Ident

val add_local_file: string -> unit

(* records definition locations *)

val set_output_dir: string option -> unit
val set_stdlib_url: string -> unit

val output_file: string -> string

val pp_anchor: kind:string -> Format.formatter -> ident -> unit
  (* raises [Not_found] if ident has no location *)

val pp_locate: kind:string -> Format.formatter -> ident -> unit
  (* raises [Not_found] if ident has no location *)
