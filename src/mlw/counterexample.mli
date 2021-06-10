(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Use solver models and Pinterp to create counterexamples *)

open Pinterp
open Model_parser
open Pmodule

(** {2 Solver's model analysis and counterexample construction} *)

val debug_check_ce : Debug.flag
(** print information about the models returned by the solver and the
   result of checking them by interpreting the program concretly and
   abstractly using the values in the solver's model *)

val debug_check_ce_summary : Debug.flag
(** Print only a summary of checking the counterexample. *)

type result_state =
  | Rnormal
    (** the execution terminated normally *)
  | Rfailure of cntr_ctx * Term.term
    (** the execution leads to a failure *)
  | Rstuck of string
    (** the model doesn't lead to a counterexample or is incosistent *)
  | Runknown of string
    (** cannot decide if the model leads to a counterexample *)

val print_result_state : result_state Pp.pp

type rac_result = {
    state    : result_state;
    exec_log : Log.exec_log;
  }
(** Result of a RAC execution comprised of a final state and the execution log.
   *)

val find_rs : pmodule -> model -> Expr.rsymbol
(** Returns the rsymbol of the procedure to which the VC term of the model
    belongs.

    @raise Failure when there is no such procedure, or the VC term location is
    empty or dummy. *)

val check_model_rs : ?timelimit:float -> ?steplimit:int -> giant_steps:bool ->
  rac_reduce_config -> Env.env -> pmodule -> model -> Expr.rsymbol -> rac_result
(** [check_model_rs ~abstract cfg env pm m rs] executes a call to the procedure
    [rs] with normal and giant-steps RAC. *)

type two_rac_results = private
  | Cannot_execute_model of {reason: string}
    (** Neither RAC could be executed  *)
  | Check_model_result of {normal: result; giant_steps: result}
    (**  *)
(** The results of the two RAC executions *)

val check_model : ?timelimit:float -> ?steplimit:int -> rac_reduce_config ->
  Env.env -> pmodule -> model -> two_rac_results
(** Run the normal and giant-step RAC on the function corresponding to the model
    (the program corresponding to the model is obtained from the location in the
    model). *)

val print_result : rac_result Pp.pp
(** Print the result of a RAC execution. *)

val print_result_with_trace : ?verb_lvl:int -> rac_result Pp.pp
(** Like [print_result] but print also the execution log *)

(** {2 Summary of checking models} *)

type verdict =
  | NC (** Non-conformity between program and annotations: the CE shows that the
           program doesn't comply to the verification goal. *)
  | SW (** Sub-contract weakness: The contracts of some function or loop are
           underspecified. *)
  | NCSW (** Non-conformity or sub-contract weakness. *)
  | BAD of string (** Bad counterexample with reason *)
  | UNKNOWN of string (** Incompleteness with reason *)

type classification = verdict * Log.exec_log
(** The result of a classification based on normal and giant-step RAC execution
    is comprised of a verdict and the execution trace of the relevant execution *)

val classify :
  vc_term_loc:Loc.position option -> vc_term_attrs:Ident.Sattr.t ->
  normal:rac_result -> giant_steps:rac_result -> classification
(** Classify a counterexample based on the resultso of the two RAC executions *)

val is_vc_term :
  vc_term_loc:Loc.position option -> vc_term_attrs:Ident.Sattr.t ->
  cntr_ctx -> Term.term -> bool

val print_classification_title : ?check_ce:bool -> classification Pp.pp

val print_classification_kind : classification Pp.pp

val print_model_classification :
  ?verb_lvl:int -> ?check_ce:bool -> ?json:[< `All | `Values ] -> (model * classification) Pp.pp
(** Print a counterexample. (When the prover model is printed and [~json:`Values] is
   given, only the values are printedas JSON.) *)

val print_result_summary : result Pp.pp -> (two_rac_results * classification) Pp.pp

(** {2 Model selection} *)

type sort_models
(** Sort prover models in [select_model]. *)

val select_model :
  ?verb_lvl:int -> ?check:bool -> ?reduce_config:rac_reduce_config ->
  ?timelimit:float -> ?steplimit:int -> ?sort_models:sort_models ->
  Env.env -> pmodule -> (Call_provers.prover_answer * model) list ->
  (model * classification) option
(** [select ~check ~conservative ~reduce_config env pm ml] chooses a model from
    [ml]. [check] is set to false by default and indicates if interpretation
    should be used to select the model. [reduce_config] is set to
    [rac_reduce_config ()] by default and is only used if [check=true]. Different
    priorizations of prover models can be selected by [sort_models], which is by
    default [prioritize_first_good_model] if [check] and
    [prioritize_last_non_empty_model] otherwise. *)

val prioritize_first_good_model : sort_models
(** If there is any model that can be verified by counterexample
    checking, prioritize NCCE over SWCE over NCCE_SWCE, and prioritize
    simpler models from the incremental list produced by the prover.

    Otherwise prioritize the last, non-empty model in the incremental
    list, but penalize bad models. *)

val prioritize_last_non_empty_model : sort_models
(** Do not consider the result of checking the counterexample model, but just
    priotize the last, non-empty model in the incremental list of models. *)

(** {3 Compatibility} *)

val select_model_last_non_empty :
  (Call_provers.prover_answer * model) list -> model option
(** Select the last, non-empty model in the incremental list of models as done
    before 2020.

    Same behaviour as
    [select_model ~check:false ~sort_models:prioritize_last_non_empty_model]. *)

(** {2 Conversion to [Model_parser.model] }*)

val model_of_exec_log : original_model:model -> Log.exec_log -> model
(** [model_of_exec_log ~original_model log)] populates a [Model_parser.model] from an
   execution log [log] *)
