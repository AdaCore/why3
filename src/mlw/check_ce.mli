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

(** {1 Validation of candidate counterexamples and classification of proof
    failures using runtime-assertion checking} *)

open Pmodule
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

type rac_result = rac_result_state * Log.exec_log
(** The result of a RAC execution is comprised of the final state and the
   execution log. *)

val string_of_rac_result_state : rac_result_state -> string
(** String of the RAC result state variant *)

val print_rac_result : ?verb_lvl:int -> rac_result Pp.pp
(** Print the result state of a RAC execution with the execution log *)

val rac_execute : Pinterp.ctx -> Expr.rsymbol -> rac_result
(** Execute a call to the program function given by the [rsymbol] using normal
    or giant-step RAC, using the given model as an oracle for program parameters
    (and during giant-steps). *)

(* (\** [check_goal config env pm model ls] checks the validity of the goal [ls]
 *     with the variable bindings from [model]. *\)
 * val check_goal : rac_config -> Env.env -> pmodule -> model ->
 *   Term.lsymbol -> bool option *)

val find_rs : pmodule -> Loc.position -> Expr.rsymbol option
(** Auxiliary function that returns the rsymbol of the procedure to which the VC
    term of the model belongs.

    The function fails (with exception [Failure]) when the VC term location of
    the model is empty or dummy, and the search cannot succeed. *)

(** {2 Conversions with models }*)

val oracle_of_model : Pmodule.pmodule -> Model_parser.model -> Pinterp_core.oracle
(** Create an oracle from a (prover model-derived) candidate counterexample. *)

val model_of_exec_log : original_model:model -> Log.exec_log -> model
(** [model_of_exec_log ~original_model log)] populates a [Model_parser.model] from an
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

val report_verdict : ?check_ce:bool -> verdict Pp.pp
(** Describe a verdict in a short sentence. *)

type classification = verdict * Log.exec_log
(** The result of a classification based on normal and giant-step RAC execution
    is comprised of a verdict itself and the log of the relevant execution. *)

val print_classification_log_or_model :
  ?verb_lvl:int -> ?json:[< `All | `Values ] ->
  print_attrs:bool -> (model * classification) Pp.pp
(** Print classification log or the model, when the model is bad or incomplete
    (When the prover model is printed and [~json:`Values] is given, only the
    values are printed as JSON.) *)

val print_model_classification :
  ?verb_lvl:int -> ?json:[< `All | `Values ] -> ?check_ce:bool ->
  (model * classification) Pp.pp
(** Print the classification with the classification log or model. *)

val classify : vc_term_loc:Loc.position option -> vc_term_attrs:Ident.Sattr.t ->
  normal_result:rac_result -> giant_step_result:rac_result -> classification
(** Classify a counterexample based on the results of the normal and giant-step
    RAC executions. *)

(* val is_vc_term : model -> (cntr_ctx * Term.term) -> bool
 * (\** [is_vc_term ~vc_term_loc ~vc_term_attrs fail] tests if the data [fail] from
 *     a failure corresponds to the sub-goal for which the model has been generated. *\) *)

(** {2 Model selection based on counterexample checking}

    Why3 requests three models from the prover, resulting in three {e candidate}
    counterexamples ({!recfield:Call_provers.prover_result.pr_models}). The
    following functions help selecting one counterexample. *)

val select_model :
  ?timelimit:float -> ?steplimit:int -> ?verb_lvl:int ->
  ?compute_term:compute_term ->
  check_ce:bool -> rac -> Env.env -> Pmodule.pmodule ->
  (Call_provers.prover_answer * model) list -> (model * classification) option
(** Select one of the given models. By default, counterexample classification
    ([check_ce]) is disabled. When counterexample checking is enabled, the first
    good model is selected (with verdict {!variant:NC}, {!variant:SW}, or
    {!variant:NC_SW}, if any), or the last non-empty model otherwise. The RAC
    reduce configuration [rac] is used only when counterexample checking is
    enabled. *)

val select_model_last_non_empty :
  (Call_provers.prover_answer * model) list -> model option
(** Select the last, non-empty model in the incremental list of models.

    This is a compatiblity function for the behaviour before 2020, and gives
    the same result as [select_model ~check_ce:false
    ~sort_models:prioritize_last_non_empty_model]. *)

(**/**)

val debug_check_ce : Debug.flag
(** print information about the models returned by the solver and the
   result of checking them by interpreting the program concretly and
   abstractly using the values in the solver's model *)

val debug_check_ce_summary : Debug.flag
(** Print only a summary of checking the counterexample. *)
