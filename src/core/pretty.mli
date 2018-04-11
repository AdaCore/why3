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

(** Pretty-printing various objects from Why3's core logic *)

val label_coercion: Ident.label

(*
val forget_all : unit -> unit     (* flush id_unique *)
val forget_tvs : unit -> unit     (* flush id_unique for type vars *)
val forget_var : vsymbol -> unit  (* flush id_unique for a variable *)
*)

val why3_keywords : string list

include Pretty_sig.Printer

val meta_introduced_hypotheses : Theory.meta

val create  : Ident.ident_printer ->Ident.ident_printer ->
              Ident.ident_printer -> Ident.ident_printer ->
              bool -> (module Pretty_sig.Printer)
