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

open Format

let default_hook ?loc s =
  Opt.iter (Loc.report_position err_formatter) loc;
  eprintf "warning: %s@." s

let hook = ref default_hook
let set_hook = (:=) hook

let emit ?loc p =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  pp_set_margin fmt 1000000000;
  pp_open_box fmt 0;
  let handle fmt =
    pp_print_flush fmt (); !hook ?loc (Buffer.contents b) in
  kfprintf handle fmt p
