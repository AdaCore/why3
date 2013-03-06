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

type driver = private {
  drv_lib         : Mlw_typing.mlw_library;
  drv_printer     : string option;
  drv_prelude     : Printer.prelude;
  drv_thprelude   : Printer.prelude_map;
  drv_blacklist   : Printer.blacklist;
  drv_syntax      : Printer.syntax_map;
}

val load_driver :
  Mlw_typing.mlw_library -> string -> string list -> driver
  (** loads a driver from a file
      @param env    environment to interpret theories and modules
      @param string driver file name
      @param string list additional drivers containing only theories/modules *)


