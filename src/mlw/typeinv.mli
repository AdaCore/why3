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

val is_trusted_constructor : Pdecl.known_map -> Term.lsymbol -> bool
val is_trusted_projection  : Pdecl.known_map -> Term.lsymbol -> Ity.ity -> bool

val inspect : Pdecl.known_map -> Term.term list -> Term.term list

val inject : Pdecl.known_map -> Term.term -> Term.term
