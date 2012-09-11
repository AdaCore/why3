(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

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
