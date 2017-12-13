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

val debug : Debug.flag

type driver = private {
  drv_env         : Env.env;
  drv_printer     : string option;
  drv_prelude     : Printer.prelude;
  drv_thprelude   : Printer.prelude_map;
  drv_blacklist   : Printer.blacklist;
  drv_syntax      : Printer.syntax_map;
  drv_converter   : Printer.syntax_map;
  drv_literal     : Printer.syntax_map;
}


type printer_args = private {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  converter   : Printer.syntax_map;
  literal     : Printer.syntax_map;
}

val load_driver : Env.env -> string -> string list -> driver
  (** loads a driver from a file
      @param env    environment to interpret theories and modules
      @param string driver file name
      @param string list additional drivers containing only theories/modules *)

type printer =
  printer_args -> ?old:in_channel -> ?fname:string -> flat:bool ->
  Pmodule.pmodule -> Mltree.decl Pp.pp

type filename_generator = ?fname:string -> Pmodule.pmodule -> string

val register_printer :
  desc:Pp.formatted -> string -> filename_generator -> printer -> unit

val lookup_printer : driver -> filename_generator * printer_args * printer

val list_printers : unit -> (string * Pp.formatted) list

(*
val extract_module : ?old:in_channel ->
   driver -> Format.formatter -> Pmodule.pmodule -> unit
 *)
