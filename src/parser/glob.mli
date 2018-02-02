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

open Ident

val flag: Debug.flag

val dummy_id: ident

val def: ident -> unit
  (** [def id] registers that [id] is defined at position [id.id_loc] *)

val use: Loc.position -> ident -> unit
  (** [use loc id] registers that [id] is used at position [loc] *)

type def_use = Def | Use

val find: Loc.position -> ident * def_use
  (** [find pos] returns the ident used/defined at position [pos], if any,
      or raises [Not_found] *)
