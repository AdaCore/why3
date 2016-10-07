(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)
open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer
open Theory
open Stdlib

type name_tables = {
    namespace : Theory.namespace;
    unique_names : string Mid.t;
    th: theory_uc;
  }

val build_name_tables : Task.task -> name_tables
