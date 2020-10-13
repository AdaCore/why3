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

(** {1 Interpreter types} *)

type env
(** Context for the interpreter *)

type result =
  | Normal of value
  | Excep of Ity.xsymbol * value
  | Irred of Expr.expr
  | Fun of Expr.rsymbol * Ity.pvsymbol list * int
(** Result of the interpreter **)

(** {1 Contradiction context} *)

type cntr_ctx = {
  c_desc: string;
  c_trigger_loc: Loc.position option;
  c_env: env
}
(** Context of a contradiction during RAC *)

exception CannotCompute of {reason: string}

exception Contr of cntr_ctx * Term.term
(** Exception [Contr] is raised when a contradiction is detected during RAC. *)

exception RACStuck of env * Loc.position option

(** {1 Configuration} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

type rac_prover
(** The configuration of the prover used for reducing terms in RAC *)

val rac_prover : Whyconf.config -> Env.env -> limit_time:int -> string -> rac_prover
(** [rac_prover cnf env limit prover s] creates a RAC prover configuration for a Why3
   prover string [s] *)

type rac_reduce_config
(** The configuration for RAC, including (optionally) a transformation for reducing terms
   (usually: compute_in_goal), and a prover to be used if the transformation does not
   yield a truth value. When neither transformation nor prover are defined, then RAC does
   not progress. *)

val rac_reduce_config :
  ?trans:Task.task Trans.tlist ->
  ?prover:rac_prover ->
  unit -> rac_reduce_config

type rac_config

val rac_config :
  do_rac:bool ->
  abstract:bool ->
  ?reduce:rac_reduce_config ->
  ?model:Model_parser.model ->
  unit -> rac_config

(** {1 Interpreter} *)

val eval_global_fundef :
  rac_config ->
  Env.env ->
  Pdecl.known_map ->
  Decl.known_map ->
  (Expr.rsymbol * Expr.cexp) list ->
  Expr.expr ->
  result * value Term.Mvs.t * value Expr.Mrs.t
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
  rac_config ->
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
  rac_reduce_config ->
  Env.env ->
  Pmodule.pmodule ->
  Model_parser.model ->
  Model_parser.check_model_result
(** [check_model env pm m] checks if model [m] is valid, i.e. the abstract
    execution using the model values triggers a RAC contradiction in the
    corresponding location. The function returns true if the corresponding
    program definition cannot be identified, or if there is an error during
    RAC execution.

    Optional arguments [rac_trans] and [rac_prover] as in [eval_global_fundef]. *)

(** {1 Reporting results} *)

val report_cntr : Format.formatter -> cntr_ctx * Term.term -> unit
val report_cntr_body : Format.formatter -> cntr_ctx * Term.term -> unit
(** Report a contradiction context and term *)

val report_eval_result :
  Expr.expr ->
  Format.formatter ->
  result * value Term.Mvs.t * value Expr.Mrs.t ->
  unit
(** Report an evaluation result *)

(**/**)

val debug_rac : Debug.flag
