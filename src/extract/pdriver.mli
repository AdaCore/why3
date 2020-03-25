(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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
  drv_thexportpre : Printer.prelude_export_map;
  drv_thinterface : Printer.interface_map;
  drv_thexportint : Printer.interface_export_map;
  drv_blacklist   : Printer.blacklist;
  drv_syntax      : Printer.syntax_map;
  drv_literal     : Printer.syntax_map;
  drv_prec        : (int list) Ident.Mid.t;
}


type printer_args = private {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  thexportpre : Printer.prelude_export_map;
  thinterface : Printer.interface_map;
  thexportint : Printer.interface_export_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  literal     : Printer.syntax_map;
  prec        : (int list) Ident.Mid.t;
}

val load_driver : Env.env -> string -> string list -> driver
  (** loads a driver from a file
      @param env    environment to interpret theories and modules
      @param string driver file name
      @param string list additional drivers containing only theories/modules *)

type filename_generator = ?fname:string -> Pmodule.pmodule -> string

type decl_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  Pmodule.pmodule -> Mltree.decl Pp.pp

(** Things to print as header/footer. *)
type border_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  Pmodule.pmodule Pp.pp

(** Things to do at the beginning of a module, e.g. open/#include.
    Only used in modular extraction. *)
type prelude_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  deps:Pmodule.pmodule list ->
  global_prelude:Printer.prelude ->
  prelude:Printer.prelude ->
  Pmodule.pmodule Pp.pp

type file_printer = {
  filename_generator : filename_generator;
  decl_printer : decl_printer;
  header_printer : border_printer;
  prelude_printer : prelude_printer;
  footer_printer : border_printer;
}

type printer = {
  desc           : Pp.formatted;
  implem_printer : file_printer;
  interf_printer : file_printer option;
  flat_printer   : file_printer;
}

val default_prelude_printer : prelude_printer

val dummy_border_printer : border_printer

val register_printer : string -> printer -> unit

val lookup_printer : driver -> printer_args * printer

val list_printers : unit -> (string * Pp.formatted) list

(*
val extract_module : ?old:in_channel ->
   driver -> Format.formatter -> Pmodule.pmodule -> unit
 *)
