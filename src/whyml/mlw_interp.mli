(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* WhyML interpretation *)

val eval_global_term: Env.env -> Decl.known_map -> Term.term -> Term.term

type result

val print_result: Format.formatter -> result -> unit

val eval_global_expr: Env.env ->
           Mlw_decl.known_map -> Decl.known_map -> Mlw_expr.expr -> result

