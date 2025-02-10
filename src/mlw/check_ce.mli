(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Validation of candidate counterexamples and classification of proof
    failures using runtime-assertion checking} *)

open Pinterp_core
open Model_parser

(** This module provides an interface for validating counterexamples and
    classifying proof failures using normal and giant-step runtime assertion
    checking, as described in the following article:

    {%html:<blockquote>%}
      Benedikt Becker, Cláudio Belo Lourenço, Claude Marché (2021):
      {e Explaining Proof Failures with Giant-Step Runtime Assertion Checking}.
    {%html:</blockquote>%}

    The objective is to validate the candidate counterexample derived from the
    prover model in {!module:Model_parser}, and to classify proof failures for
    valid counterexamples (see type {!verdict}).*)

(** {2 RAC execution}

    An interface to the Why3 interpreter in {!Pinterp} with normal and
    giant-step runtime-assertion checking (RAC) for counterexample checking. *)

type rac_result_state =
  | Res_normal
  (** The execution terminated normally *)
  | Res_fail of cntr_ctx * Term.term
  (** The execution terminated due to a failed assertion *)
  | Res_stuck of string
  (** The execution terminated due to a failed assumption *)
  | Res_incomplete of string
  (** The execution could not be terminated due to incompleteness in the
     execution or oracle *)
(** The result state of a RAC execution *)

val print_rac_result_state : rac_result_state Pp.pp
(** Print a RAC result state *)

type rac_result =
  | RAC_not_done of string
(** RAC has not be done for the reason given as argument.
    Possible reasons include:
    - the VC has no identified source location,
    - the identified source location cannot be associated to a program routine,
    - a small-step RAC has not been executed because only the giant-step one
      was requested. *)
  | RAC_done of rac_result_state * Log.exec_log
(** The result of a RAC execution includes the final state and the
   execution log. *)

val string_of_rac_result_state : rac_result_state -> string
(** String of the RAC result state variant *)

val print_rac_result : ?verb_lvl:int -> rac_result Pp.pp
(** Print the result state of a RAC execution with the execution log *)

val rac_execute : Pinterp.ctx -> Expr.rsymbol -> rac_result_state * Log.exec_log
(** Execute a call to the program function given by the [rsymbol] using normal
    or giant-step RAC, using the given model as an oracle for program parameters
    (and during giant-steps). *)

(** {2 Conversions with models }*)

val oracle_of_model : Pmodule.pmodule -> Model_parser.model -> Pinterp_core.oracle
(** Create an oracle from a (prover model-derived) candidate counterexample. *)

val model_of_exec_log : original_model:model -> Log.exec_log -> model
(** [model_of_exec_log ~original_model log)] populates a {!Model_parser.model} from an
   execution log [log] *)

(* val find_ls : Theory.theory -> Loc.position -> Term.lsymbol *)

(** {2 Counterexample validation and proof failure classification} *)

type verdict =
  | NC (** Non-conformity between program and annotations: the counterexample
           shows that the program doesn't comply to the verification goal. *)
  | SW (** Sub-contract weakness: the counterexample shows that the contracts of
           some function or loop are too weak. *)
  | NC_SW (** A non-conformity or a sub-contract weakness. *)
  | BAD_CE of string (** Bad counterexample, the string gives a reason. *)
  | INCOMPLETE of string (** Incompleteness, the string gives a reason. *)
(** Verdict of the classification. The verdicts [NC], [SW], and [NC_SW] are said
    to be {e valid}. *)

val string_of_verdict : verdict -> string
(** The variant name of the verdict as a string. *)

type classification = verdict * Log.exec_log
(** The result of a classification based on normal and giant-step RAC execution
    is comprised of a verdict itself and the log of the relevant execution. *)

val report_verdict : Env.env -> classification Pp.pp
(** Describe a verdict in a short sentence. *)

val print_classification_log_or_model :
  ?verb_lvl:int -> json:bool ->
  print_attrs:bool -> (model * classification) Pp.pp
(** Print classification log or the model when the model is bad or the verdict
    is INCOMPLETE *)

val print_model_classification :
  ?verb_lvl:int -> json:bool -> Env.env -> (model * classification) Pp.pp
(** Print the classification with the classification log or model. *)

val classify : vc_term_loc:Loc.position option -> vc_term_attrs:Ident.Sattr.t ->
  normal_result:rac_result_state * Log.exec_log ->
  giant_step_result:rac_result_state * Log.exec_log ->
  classification
(** Classify a counterexample based on the results of the normal and giant-step
    RAC executions. *)

(* val is_vc_term : model -> (cntr_ctx * Term.term) -> bool
 * (\** [is_vc_term ~vc_term_loc ~vc_term_attrs fail] tests if the data [fail] from
 *     a failure corresponds to the sub-goal for which the model has been generated. *\) *)

(** {2 Model selection based on counterexample checking}

    Why3 requests three models from the prover, resulting in three {e candidate}
    counterexamples ({!recfield:Call_provers.prover_result.pr_models}). The
    following functions help selecting one counterexample. *)

val models_from_rac : limits:Call_provers.resource_limits ->
?verb_lvl:int -> ?compute_term:compute_term -> rac -> Env.env -> Pmodule.pmodule ->
(Call_provers.prover_answer * model) list -> (model * rac_result * rac_result * classification) list

(** Execute small and giant-step RAC on the models, and compute the classification.
    The computed [classification] is based on the results of the normal and giant
    step RAC executions, and contains the relevant execution logs. This log can be
    used to explain the classification.
    The returned [model] list contains the prover supplide models, where we update
    the values to those that have been computed by the small-step RAC. The [model]
    is provided as an easier to manipulate object than the log, but it might contain
    several inconsistencies; in particular, only the [me_concrete_value] fields of the
    model are guaranteed to be updated. *)

val models_from_giant_step :
  limits:Call_provers.resource_limits -> ?verb_lvl:int ->
  ?compute_term:compute_term -> rac -> Env.env -> Pmodule.pmodule ->
  (Call_provers.prover_answer * model) list ->
  (model * rac_result) list
(** Execute only the giant-step RAC. The returned [rac_result] contains a trace of the
    execution of the RAC, and can be used for displaying to the user or to further elaborate
    the counterexample.  As a helper mechanism, we also return a new [model]. See the
    discussion on [models_from_rac] for a more in-depth explanation. *)

val best_rac_result : (model * rac_result * rac_result * classification) list -> (model * classification) option
(** Select a model based on the classification (itself based on the normal and
    giant-step RAC executions). The [rac_result] are just discarded, as the classification
    is calculated at the previous stage.

    The first good model is selected (i.e. with verdict {!const:verdict.NC},
    {!const:verdict.SW}, or {!const:verdict.NC_SW}, if any).
    *)

val best_giant_step_result : (model * rac_result) list -> (model * rac_result) option
(** Select the best non empty model based on the result of the giant-step RAC
    execution, with the following classification:
    RAC_done (Res_fail _ , _) > RAC_done (Res_normal, _)
                              > RAC_done (Res_stuck _ , _)
                              > RAC_done (Res_incomplete _ , _)
                              > RAC_not_done _
    *)

val last_nonempty_model : (Call_provers.prover_answer * model) list -> model option
(** Select the last non-empty model from the list of models. Helper function for the
    cases where counterexample checking has not been requested. *)

(** {Debugging flags} *)

val debug_check_ce_rac_results : Debug.flag
(** Print information about the models returned by the solver and the
   results of checking them by interpreting the program concretly and
   abstractly using the values in the solver's model. *)

val debug_check_ce_categorization : Debug.flag
(** Print the result of the categorization computed from the results of
    the concrete and abstract RAC executions. *)
