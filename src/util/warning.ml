(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Util

let default_hook ?loc s =
  option_iter (Loc.report_position err_formatter) loc;
  eprintf "warning: %s@." s

let hook = ref default_hook
let set_hook = (:=) hook

let emit ?loc p =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  let handle fmt =
    Format.pp_print_flush fmt (); !hook ?loc (Buffer.contents b) in
  kfprintf handle fmt p
