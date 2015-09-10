(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* WhyML interpretation *)

type value

val print_value: Format.formatter -> value -> unit

val eval_global_term:
  Env.env -> Decl.known_map -> Term.term -> value

val eval_global_symbol:
  Env.env -> Mlw_module.modul -> Format.formatter -> Mlw_expr.fun_defn -> unit
