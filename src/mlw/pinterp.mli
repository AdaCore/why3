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

(*
val eval_global_term:
  Env.env -> Decl.known_map -> Term.term -> value
*)

type result =
  | Normal of value
  | Excep of Ity.xsymbol * value
  | Irred of Expr.expr
  | Fun of  Expr.rsymbol *  Ity.pvsymbol list * int

(*
val eval_global_expr:
  Env.env -> Pdecl.known_map -> Decl.known_map -> 'a ->
  Expr.expr -> result (* * value Term.Mvs.t *)
*)

val eval_global_symbol:
  Env.env -> Pmodule.pmodule -> Format.formatter -> Expr.rsymbol -> unit
