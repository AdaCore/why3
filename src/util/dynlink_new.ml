(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let loadfile name =
  try
    Dynlink.loadfile name
  with
  | Dynlink.Error (Dynlink.Library's_module_initializers_failed e) ->
      Printexc.raise_with_backtrace e (Printexc.get_raw_backtrace ())
