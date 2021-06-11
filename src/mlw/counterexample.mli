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

(** {1 Validation of counterexamples and classification of proof failures using
    runtime-assertion checking}

    This module provides an interface for validating counterexamples and
    classifying proof failures using normal and giant-step runtime assertion
    checking, as described in the following article:

    {%html:<blockquote>%}
      Benedikt Becker, Cláudio Belo Lourenço, Claude Marché (2021):
      {e Explaining Proof Failures with Giant-Step Runtime Assertion Checking}.
    {%html:</blockquote>%} *)

open Pinterp
open Model_parser
open Pmodule

(** {2 RAC execution}

    The module {!Pinterp} provides an Why3 interpreter with normal and
    giant-step runtime-assertion checking (RAC). Here is an interface for easier
    use in counterexample checking. *)

type rac_result_state =
  | Normal
  (** The execution terminated normally *)
  | Fail of cntr_ctx * Term.term
  (** The execution terminated due to a failed assertion *)
  | Stuck of string
  (** The execution terminated due to a failed assumption *)
  | Incomplete of string
  (** The execution could not be terminated due to incompleteness in the
     execution or oracle *)
(** The result state of a RAC execution *)

val print_rac_result_state : rac_result_state Pp.pp
(** Print a RAC result state *)

type rac_result = rac_result_state * Log.exec_log
(** The result of a RAC execution is comprised of the final state and the
   execution log. *)

val print_rac_result : ?verb_lvl:int -> rac_result Pp.pp
(** Print the result state of a RAC execution with the execution log *)

val rac_execute :
  ?timelimit:float -> ?steplimit:int -> ?rac:rac_config ->
  giant_steps:bool -> Env.env -> pmodule -> model -> Expr.rsymbol -> rac_result
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

    It raises exception [Failure] when the VC term location of the model is
    empty or dummy, and the search cannot succeed. *)

(* val find_ls : Theory.theory -> Loc.position -> Term.lsymbol *)

(** {2 Counterexample validation and proof failure classification} *)

type classification =
  | NC (** Non-conformity between program and annotations: the counterexample
           shows that the program doesn't comply to the verification goal. *)
  | SW (** Sub-contract weakness: the counterexample shows that the contracts of
           some function or loop are too weak. *)
  | NC_SW (** A non-conformity or a sub-contract weakness. *)
  | BAD_CE of string (** Bad counterexample, the string gives a reason. *)
  | INCOMPLETE of string (** Incompleteness, the string gives a reason. *)
(** Classification of counterexample checking. *)

val string_of_classification : classification -> string
(** The variant name of the classification as a string. *)

val print_classification_description : ?check_ce:bool -> classification Pp.pp
(** Print a short sentence describing the classification. *)

type classification_result = classification * Log.exec_log
(** The result of a classification based on normal and giant-step RAC execution
    is comprised of the classification itself and the log of the relevant
    execution. *)

val classify : vc_term_loc:Loc.position option -> vc_term_attrs:Ident.Sattr.t ->
  normal_result:rac_result -> giant_step_result:rac_result -> classification_result
(** Classify a counterexample based on the results of the normal and giant-step
    RAC executions. *)

(* val is_vc_term : model -> (cntr_ctx * Term.term) -> bool
 * (\** [is_vc_term ~vc_term_loc ~vc_term_attrs fail] tests if the data [fail] from
 *     a failure corresponds to the sub-goal for which the model has been generated. *\) *)

(** {2 Model selection based on counterexample checking}

    In Why3 requests three models from the prover, resulting in three candidate
    counterexamples (field [pr_models] in [Call_provers.prover_result]). The
    following functions help selecting one model using a selection strategy that
    may use the results from the counterexample classifications.
 *)

type strategy
(** Strategy to select a model. *)

val prioritize_first_good_model : strategy
(** If there is any model that can be verified by counterexample checking,
    prioritize non-conformity over subcontract-weakness over non-conformity or
    subcontract weakness, and prioritize simpler models from the incremental list
    produced by the prover.

    Otherwise prioritize the last, non-empty model in the incremental list, but
    penalize bad models. *)

(** Do not consider the result of checking the counterexample model, but just
    priotize the last, non-empty model in the incremental list of models. *)
val prioritize_last_non_empty_model : strategy

val select_model :
  ?check_ce:bool -> ?rac:rac_config ->
  ?timelimit:float -> ?steplimit:int -> ?verb_lvl:int ->
  ?strategy:strategy ->
  Env.env -> pmodule -> (Call_provers.prover_answer * model) list ->
  (model * classification_result) option
(** Chose one of the given models based on given the strategy. By default,
    counterexample classification ([check_ce]) is disabled. The RAC reduce
    configuration [rac] is used only when counterexample checking is
    enabled. The selection strategies is [prioritize_first_good_model] by
    default when counterexample checking is enabled, and
    [prioritize_last_non_empty_model] otherwise. *)

val select_model_last_non_empty :
  (Call_provers.prover_answer * model) list -> model option
(** Select the last, non-empty model in the incremental list of models.

    This is a compatiblity function for the behaviour before 2020, and gives
    the same result as [select_model ~check_ce:false
    ~sort_models:prioritize_last_non_empty_model]. *)

(** {2 Conversion to [Model_parser.model] }*)

val model_of_exec_log : original_model:model -> Log.exec_log -> model
(** [model_of_exec_log ~original_model log)] populates a [Model_parser.model] from an
   execution log [log] *)

(**/**)

val debug_check_ce : Debug.flag
(** print information about the models returned by the solver and the
   result of checking them by interpreting the program concretly and
   abstractly using the values in the solver's model *)

val debug_check_ce_summary : Debug.flag
(** Print only a summary of checking the counterexample. *)

val print_classification_log_or_model :
  ?verb_lvl:int -> ?json:[< `All | `Values ] ->
  print_attrs:bool -> (model * classification_result) Pp.pp
(** Print a counterexample. (When the prover model is printed and [~json:`Values] is
   given, only the values are printed as JSON.) *)

val print_model_classification :
  ?verb_lvl:int -> ?json:[< `All | `Values ] -> ?check_ce:bool ->
  (model * classification_result) Pp.pp
