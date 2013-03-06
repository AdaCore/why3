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

open Ident

val flag: Debug.flag

val dummy_id: ident

val use: Loc.position -> ident -> unit
  (** [add loc id] registers that [id] was used at position [loc] *)

val locate: string * int * int -> ident
  (** [locate pos] returns the ident used at position [pos], if any,
      or raises [Not_found] *)
