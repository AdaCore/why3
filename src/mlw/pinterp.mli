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

(** Interpreter context *)
type env

(** {1 Contradiction context} *)

(** Context of a contradiction during RAC *)
type cntr_ctx =
  { c_desc: string;
    c_trigger_loc: Loc.position option;
    c_env: env }

(** Exception [Contr] is raised when a contradiction is observed
    during RAC. *)
exception Contr of cntr_ctx * Term.term

(** {1 Global evaluation} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

(* TODO Replace options rac_trans and rac_prover by a strategy *)

type rac_prover

val rac_prover : Whyconf.config -> Env.env -> limit_time:int -> string -> rac_prover

val eval_global_fundef :
  rac:bool ->
  ?rac_trans:Task.task Trans.tlist ->
  ?rac_prover:rac_prover ->
  Env.env ->
  Pdecl.known_map ->
  Decl.known_map ->
  (Expr.rsymbol * Expr.cexp) list ->
  Expr.expr ->
  result * value Term.Mvs.t
(** [eval_global_fundef ~rac env disp_ctx known def] evaluates a function definition and
   returns an evaluation result and a final variable environment.

    During RAC, annotations are first reduced by applying transformation [rac_trans], and
   if the transformation doesn't return to a trivial formula ([true]/[false]), the prover
   [rac_prover] is applied. Pure expressions and pure executions are reduced only using
   [rac_trans]. When neither [rac_trans] or [rac_prover] are defined, RAC does not
    progress.

    @raise Contr RAC is enabled and a contradiction was found *)

(** {1 Check counter-example models using RAC}*)

val check_model_rs :
  ?abs:bool ->                          (* execute abstractly *)
  ?rac_trans:Task.task Trans.tlist ->
  ?rac_prover:rac_prover ->
  Env.env ->
  Pmodule.pmodule ->
  Model_parser.model ->
  Expr.rsymbol ->
  Model_parser.full_verdict
(** [check_model_rs env pm loc m rs] checks if executing the definition of
    [rs] (abstractly) using the values from the counter-example model [m]
    trigger a RAC contradiction at location [loc].

    Optional arguments [rac_trans] and [rac_prover] as in [eval_global_fundef]. *)

val check_model :
  ?rac_trans:Task.task Trans.tlist ->
  ?rac_prover:rac_prover ->
  Env.env ->
  Pmodule.pmodule ->
  Model_parser.model ->
  Model_parser.full_verdict list
(** [check_model env pm m] checks if model [m] is valid, i.e. the abstract
    execution using the model values triggers a RAC contradiction in the
    corresponding location. The function returns true if the corresponding
    program definition cannot be identified, or if there is an error during
    RAC execution.

    Optional arguments [rac_trans] and [rac_prover] as in [eval_global_fundef]. *)

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
