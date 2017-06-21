(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val emit:
  ?loc:Loc.position -> ('b, Format.formatter, unit, unit) format4 -> 'b

(* The default behavior is to emit warning on standard error,
   with position on a first line (if any) and message on a second line.
   This can be changed using the following function. *)

val set_hook: (?loc:Loc.position -> string -> unit) -> unit


