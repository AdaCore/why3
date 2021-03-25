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
  | Rnormal (** the execution terminated normally *)
  | Rfailure (** the execution leads to a failure for the VC *)
  | Rstuck (** the model doesn't lead to a counterexample or is incosistent *)
  | Runknown (** cannot decide if the model leads to a counterexample *)

val print_result_state : result_state Pp.pp

type result = {
    state    : result_state;
    reason   : string;
    exec_log : Log.exec_log;
  }

type check_model_result = private
  | Cannot_check_model of {reason: string}
  (* the model cannot be checked (e.g. it doesn't contain a location) *)
  | Check_model_result of {abstract: result; concrete: result}
  (* the model was checked *)

val check_model : ?timelimit:float -> ?steplimit:int ->
  rac_reduce_config -> Env.env -> pmodule -> model -> check_model_result
(* interpret concrecly and abstractly the program corresponding to the
   model (the program corresponding to the model is obtained from the
   location in the model) *)

val print_full_verdict : ?verb_lvl:int -> result Pp.pp

(** {2 Summary of checking models} *)

type ce_summary =
  | NC of Log.exec_log
  (** Non-conformity between program and annotations: the CE shows that the
      program doesn't comply to the verification goal. *)
  | SW of Log.exec_log
  (** Sub-contract weakness: The contracts of some function or loop are
      underspecified. *)
  | NCSW of Log.exec_log
  (** Non-conformity or sub-contract weakness. *)
  | BAD
  (** Bad counterexample. *)
  | UNKNOWN of string
  (** The counterexample has not been verified. *)

val ce_summary : check_model_result -> ce_summary

val print_ce_summary_title : ?check_ce:bool -> ce_summary Pp.pp

val print_ce_summary_kind : ce_summary Pp.pp

val print_counterexample :
  ?verb_lvl:int -> ?check_ce:bool -> ?json:[< `All | `Values ] -> (model * ce_summary) Pp.pp
(** Print a counterexample. (When the prover model is printed and [~json:`Values] is
   given, only the values are printedas JSON.) *)

val print_result_summary : result Pp.pp -> (check_model_result * ce_summary) Pp.pp

(** {2 Model selection} *)

type sort_models
(** Sort prover models in [select_model]. *)

val select_model :
  ?verb_lvl:int -> ?check:bool -> ?reduce_config:rac_reduce_config ->
  ?timelimit:float -> ?steplimit:int -> ?sort_models:sort_models ->
  Env.env -> pmodule -> (Call_provers.prover_answer * model) list ->
  (model * ce_summary) option
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
  (Call_provers.prover_answer * model) list -> (model * ce_summary) option
(** Select the last, non-empty model in the incremental list of models as done
    before 2020. The summary is included for compatibility with [select_model]
    and is always [UNKNOWN].

    Same behaviour as
    [select_model ~check:false ~sort_models:prioritize_last_non_empty_model]. *)

(** {2 Conversion to [Model_parser.model] }*)

val model_of_exec_log : original_model:model -> Log.exec_log -> model
(** [model_of_exec_log ~original_model log)] populates a [Model_parser.model] from an
   execution log [log] *)
