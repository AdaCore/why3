(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

type anchor = string

val anchor: ident -> string

type url = string

val locate: ident -> url
  (* or raises [Not_found] *)

