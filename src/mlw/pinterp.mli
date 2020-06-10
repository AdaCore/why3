(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* WhyML interpretation *)

type value

val v_ty : value -> Ty.ty

val print_value : Format.formatter -> value -> unit

type result =
  | Normal of value
  | Excep of Ity.xsymbol * value
  | Irred of Expr.expr
  | Fun of Expr.rsymbol * Ity.pvsymbol list * int

type cntr_ctx =
  { c_desc : string;
    c_trigger_loc : Loc.position option;
    c_env : Env.env;
    c_known : Decl.known_map;
    c_rule_terms : Term.term Ident.Mid.t;
    c_vsenv : Term.term Term.Mvs.t }
(** Context of a contradiction during RAC *)

exception Contr of cntr_ctx * Term.term
(** Exception [Contr] is raised when a contradiction is observed
    during RAC. *)

type dispatch

val empty_dispatch : dispatch

val add_dispatch : Env.env -> dispatch -> (string * string) * (string * string) -> dispatch

exception Missing_dispatch of string

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

val find_global_symbol :
  Pmodule.pmodule Wstdlib.Mstr.t ->
  mod_name:Wstdlib.Mstr.key ->
  fun_name:string ->
  Pmodule.pmodule * Expr.rsymbol

val find_global_fundef :
  Pdecl.pdecl Ident.Mid.t ->
  Expr.rsymbol ->
  (Expr.rsymbol * Expr.cexp) list * Expr.expr
(** [find_function_definition known rs] returns a pair of [locals, body] of the body of a
    function definition and the other definitions when [rs] is defined by mutual recursion.

    @raise Not_found Symbol [rs] not found or not a function definition *)

val eval_global_fundef :
  rac:bool ->
  Env.env ->
  dispatch ->
  Pdecl.pdecl Ident.Mid.t ->
  (Expr.rsymbol * Expr.cexp) list ->
  Expr.expr ->
  result * value Term.Mvs.t
(** [eval_global_fundef ~rac env dispatch known def] evaluates a function definition and
   returns an evaluation result and a final variable environment.

    @raise Contr RAC is enabled and a contradiction was found *)

val report_eval_result :
  mod_name:string ->
  fun_name:string ->
  Expr.expr ->
  Format.formatter ->
  result * value Term.Mvs.t ->
  unit
(** Report an evaluation result *)

val report_cntr :
  mod_name:string ->
  fun_name:string ->
  Expr.expr ->
  Format.formatter ->
  cntr_ctx * Term.term ->
  unit
(** Report a contradiction context and term *)
