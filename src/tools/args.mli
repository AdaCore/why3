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

val initialize :
  ?extra_help : (Format.formatter -> unit -> unit) ->
  (string * Arg.spec * string) list ->
  (string -> unit) -> string -> Env.env * Whyconf.config

val exit_with_usage : (string * Arg.spec * string) list -> string -> 'a
