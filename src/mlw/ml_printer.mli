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

open Pp
open Printer
open Mltree

val protect_on :
  bool -> ('a, 'b, 'c, 'd, 'e, 'f) format6 -> ('a, 'b, 'c, 'd, 'e, 'f) format6

val star : unit pp

val print_list2 : unit pp -> unit pp -> 'a pp -> 'b pp -> ('a list * 'b list) pp

type info = private {
  info_syn          : syntax_map;
  info_literal      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
  info_flat         : bool;
  info_current_ph   : string list; (* current path *)
}

val create_info :
  Pdriver.printer_args -> string option -> flat:bool -> Pmodule.pmodule -> info

val add_current_path : info -> string -> info

val check_val_in_drv : info -> Expr.rsymbol -> unit

module type S = sig
  val iprinter : Ident.ident_printer
  val aprinter : Ident.ident_printer
  val tprinter : Ident.ident_printer

  val forget_id : Ident.ident -> unit
  val _forget_ids : Ident.ident list -> unit
  val forget_var : Mltree.var -> unit
  val forget_vars : Mltree.var list -> unit
  val forget_let_defn : Mltree.let_def -> unit
  val forget_pat : Mltree.pat -> unit

  val print_global_ident :
    sanitizer:(string -> string) -> Format.formatter -> Ident.ident -> unit
  val print_path : sanitizer:(string -> string) -> Format.formatter ->
    string list * Ident.ident -> unit

  val print_lident : info -> Format.formatter -> Ident.Sid.elt -> unit
  val print_uident : info -> Format.formatter -> Ident.Sid.elt -> unit

  val print_tv : Format.formatter -> Ty.tvsymbol -> unit
  val print_rs : info -> Format.formatter -> Expr.rsymbol -> unit

  val check_type_in_drv : info -> Ident.ident -> unit

  val print_ty : ?paren:bool -> info -> ty pp
end

module MLPrinter (K: sig val keywords : string list end) : S
