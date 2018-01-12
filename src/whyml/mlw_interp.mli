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

(* WhyML interpretation *)

type value

val print_value: Format.formatter -> value -> unit

val eval_global_term:
  Env.env -> Decl.known_map -> Term.term -> value

type result =
  | Normal of value
  | Excep of Mlw_ty.xsymbol * value
  | Irred of Mlw_expr.expr
  | Fun of  Mlw_expr.psymbol *  Mlw_ty.pvsymbol list * int

val eval_global_expr:
  Env.env -> Mlw_decl.known_map -> Decl.known_map -> 'a ->
  Mlw_expr.expr -> result * value Term.Mvs.t

val eval_global_symbol:
  Env.env -> Mlw_module.modul -> Format.formatter -> Mlw_expr.fun_defn -> unit
