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


val why3_keywords : string list

include Pretty_sig.Printer

val create  : Ident.ident_printer ->Ident.ident_printer ->
              Ident.ident_printer -> Ident.ident_printer ->
              bool -> (module Pretty_sig.Printer)
