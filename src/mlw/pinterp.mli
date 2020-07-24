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

(** {1 Values and results} *)

type value

val v_ty : value -> Ty.ty
val print_value : Format.formatter -> value -> unit

type result =
  | Normal of value
  | Excep of Ity.xsymbol * value
  | Irred of Expr.expr
  | Fun of Expr.rsymbol * Ity.pvsymbol list * int

(** {1 Contradiction context} *)

(** Context of a contradiction during RAC *)
type cntr_ctx =
  { c_desc: string;
    c_trigger_loc: Loc.position option;
    c_env: Env.env;
    c_known: Decl.known_map;
    c_rule_terms: Term.term Ident.Mid.t;
    c_vsenv: Term.term Term.Mvs.t }

(** Exception [Contr] is raised when a contradiction is observed
    during RAC. *)
exception Contr of cntr_ctx * Term.term

exception AbstractExEnded of Loc.position option
(* the abstract execution cannot continue *)

exception InvCeInfraction of Loc.position option
(* the counter-example model is not consistent with an invariant *)

(** {1 Global evaluation} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

val eval_global_fundef :
  rac:bool ->
  Env.env ->
  Pdecl.known_map ->
  Decl.known_map ->
  (Expr.rsymbol * Expr.cexp) list ->
  Expr.expr ->
  result * value Term.Mvs.t
(** [eval_global_fundef ~rac env disp_ctx known def] evaluates a function definition and
   returns an evaluation result and a final variable environment.

    @raise Contr RAC is enabled and a contradiction was found *)

exception CannotImportModelValue of string

val eval_rs :
  abs:bool -> (* execute abstractly *)
  Env.env ->
  Pdecl.known_map ->
  Decl.known_map ->
  Model_parser.model ->
  Expr.Mrs.key ->
  result

val maybe_ce_model_rs :
  Env.env ->
  Pmodule.pmodule ->
  Model_parser.model ->
  Expr.rsymbol ->
  bool option
(** [maybe_model_rs env pm loc m rs] checks if executing the definition of
    [rs] (abstractly) using the values from the counter-example model [m]
    trigger a RAC contradiction at location [loc]. *)

val maybe_ce_model : Env.env -> Pmodule.pmodule -> Model_parser.model -> bool
(** [maybe_ce_model env pm m] checks if model [m] is valid, i.e. the abstract
    execution using the model values triggers a RAC contradiction in the
    corresponding location. The function returns true if the corresponding
    program definition cannot be identified, or if there is an error during
    RAC execution *)

(** {1 Reporting results} *)

val report_eval_result :
  Expr.expr ->
  Format.formatter ->
  result * value Term.Mvs.t ->
  unit
(** Report an evaluation result *)

val report_cntr :
  Expr.expr ->
  Format.formatter ->
  cntr_ctx * Term.term ->
  unit
(** Report a contradiction context and term *)

(**/**)

val debug_rac : Debug.flag
