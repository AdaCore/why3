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

(** The aim of this translation is to obtain terms where all epsilon
    abstractions are closed *)

(** We do this by applying the following rewriting rule:
  eps x.P(x) => eps F.(P(F@y_1@...@y_n)) where y_1...y_n are
  the free variables in P and @ is the higher-order application symbol. *)

open Term

type lambda_match =
  | Flam of vsymbol list * trigger * term
  | Tlam of vsymbol list * trigger * term
  | LNone


val destruct_lambda : term -> lambda_match
val is_lambda : term -> bool
