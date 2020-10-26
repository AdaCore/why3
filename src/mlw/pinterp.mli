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

open Term
open Ident

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

(** {1 Interpretation log} *)

type verdict = Good_model | Bad_model | Dont_know

type exec_kind = ExecAbstract | ExecConcrete

type log_entry_desc =
  | Val_from_model of (ident * value)
  (** values taken from model during interpretation *)
  | Exec_call of (Expr.rsymbol option * value Mvs.t  * exec_kind)
  (** executed function call or lambda if no rsymbol,
      arguments, execution type*)
  | Exec_pure of (lsymbol * exec_kind)
  (** executed pure function call *)
  | Exec_any of value
  (** execute any function call *)
  | Exec_loop of exec_kind
  (** execute loop *)
  | Exec_stucked of (string * value Mid.t)
  (** stucked execution information *)
  | Exec_failed of (string * value Mid.t)
  (** failed execution information *)
  | Exec_ended
  (** execution terminated normally *)

type log_entry = {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
}

type exec_log

val print_log : json:bool -> exec_log Pp.pp

val sort_log_by_loc : exec_log -> log_entry list Wstdlib.Mint.t Wstdlib.Mstr.t

type full_verdict = {
    verdict  : verdict;
    reason   : string;
    exec_log : exec_log;
  }

val print_verdict : verdict Pp.pp
val print_full_verdict : full_verdict Pp.pp

(** Checking a model either results in a reason why it was not possible or a full
    verdict from abstract and concrete RAC *)
type check_model_result =
  | Cannot_check_model of {reason: string}
  | Check_model_result of {abstract: full_verdict; concrete: full_verdict}

val print_check_model_result : check_model_result Pp.pp

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

val rac_prover : command:string -> Driver.driver -> Call_provers.resource_limit -> rac_prover

type rac_reduce_config
(** The configuration for RAC, including (optionally) a transformation for reducing terms
   (usually: compute_in_goal), and a prover to be used if the transformation does not
   yield a truth value. When neither transformation nor prover are defined, then RAC does
   not progress. *)

val rac_reduce_config :
  ?trans:Task.task Trans.tlist ->
  ?prover:rac_prover ->
  unit -> rac_reduce_config

val rac_reduce_config_lit :
  Whyconf.config ->
  Env.env ->
  Call_provers.rac_reduce_config_lit ->
  rac_reduce_config

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
  full_verdict
(** [check_model_rs env pm loc m rs] checks if executing the definition of
    [rs] (abstractly) using the values from the counter-example model [m]
    trigger a RAC contradiction at location [loc].

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
