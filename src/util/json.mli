(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val string : Format.formatter -> string -> unit
val int : Format.formatter -> int -> unit
val bool : Format.formatter -> bool -> unit

val list :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

val map_bindings :
  ('a -> string) -> 
  (Format.formatter -> 'b -> unit) -> 
  Format.formatter ->
  ('a * 'b) list ->
  unit

val print_json_field :
  string -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
