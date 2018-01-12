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

(* OCaml program extraction *)

val debug: Debug.flag

val extract_filename: ?fname:string -> Theory.theory -> string

val extract_theory:
  Mlw_driver.driver -> ?old:Pervasives.in_channel -> ?fname:string ->
  Format.formatter -> Theory.theory -> unit

val extract_module:
  Mlw_driver.driver -> ?old:Pervasives.in_channel -> ?fname:string ->
  Format.formatter -> Mlw_module.modul -> unit

