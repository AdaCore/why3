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

val subst_filtered : subst_proxy:bool ->
  (Term.lsymbol -> bool) -> Task.task Trans.trans
(* [subst_filtered subst_proxy p]: substitute only lsymbol chosen by [p].
   If [subst_proxy] is true, allow the substitution of proxy symbols into
   non-proxy symbols.
*)

val subst : Term.term list -> Task.task Trans.trans

val subst_all : Task.task Trans.trans
