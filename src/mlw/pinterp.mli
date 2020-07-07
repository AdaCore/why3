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

(** {1 Dispatch}

    Dispatch abstract modules, which cannot be executed due to abstract types or
    val functions, to executable modules. *)

type dispatch_ctx

val empty_dispatch : dispatch_ctx

val add_dispatch :
  source:Pmodule.pmodule ->
  target:Pmodule.pmodule ->
  dispatch_ctx ->
  dispatch_ctx

(** Raised when the a module is being dispatch but an function or value is not
    defined in the target module *)
exception Missing_dispatch of string

(** {1 Evaluation} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

val eval_global_fundef :
  rac:bool ->
  Env.env ->
  dispatch_ctx ->
  Pdecl.pdecl Ident.Mid.t ->
  (Expr.rsymbol * Expr.cexp) list ->
  Expr.expr ->
  result * value Term.Mvs.t
(** [eval_global_fundef ~rac env disp_ctx known def] evaluates a function definition and
   returns an evaluation result and a final variable environment.

    @raise Contr RAC is enabled and a contradiction was found *)

exception CannotImportModelValue of string

val eval_rs : Env.env -> Pdecl.known_map -> Loc.position -> Model_parser.model -> Expr.Mrs.key -> result

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
