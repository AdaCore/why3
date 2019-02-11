(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val destruct: recursive:bool -> Decl.prsymbol -> Task.task Trans.tlist
(** [destruct ~recursive H]: On an axiom, destruct the head term of an
    hypothesis if it is either conjunction, disjunction or exists.
    If [recursive] is true, the term is recursively traversed which lead to more
    splitting.

    Efficiency: This is not optimized to be used on very big/deep
    disjunctions/conjunctions mixed.
*)
