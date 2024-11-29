(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident

val flag : Debug.flag

val def : kind:string -> ident -> unit
(** [def id] registers that [id] is defined at position [id.id_loc] *)

val use : kind:string -> Loc.position -> ident -> unit
(** [use loc id] registers that [id] is used at position [loc] *)

val clear : string -> unit
(** [clear file] clears the identifiers of [file] *)

type def_use = Def | Use

val find : Loc.position -> ident * def_use * string
(** [find pos] returns the ident at position [pos], if any, as well as its
    used/defined status and its kind, or raises [Not_found] *)

type state

val drop : string -> state
(** [drop file] clears the identifiers of [file] but preserves them *)

val restore : string -> state -> unit
(* [restore file idents] restores the identifiers of [file] *)
