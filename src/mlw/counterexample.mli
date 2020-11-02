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

(** Use solver models and Pinterp to create counterexamples *)

open Format
open Pinterp
open Model_parser
open Pmodule

(** {2 Solver's model analysis and counterexample construction} *)

val debug_check_ce : Debug.flag
(** print information about the models returned by the solver and the
   result of checking them by interpreting the program concretly and
   abstractly using the values in the solver's model *)


type verdict = private
  | Good_model (* the model leads to a counterexample *)
  | Bad_model  (* the model doesn't lead to a counterexample *)
  | Dont_know  (* cannot decide if the model leads to a counterexample *)

type full_verdict = private {
    verdict  : verdict;
    reason   : string;
    exec_log : Log.exec_log;
  }

type check_model_result = private
  | Cannot_check_model of {reason: string}
  (* the model cannot be checked (e.g. it doesn't contain a location) *)
  | Check_model_result of {abstract: full_verdict; concrete: full_verdict}
  (* the model was checked *)

val check_model :
  rac_reduce_config -> Env.env -> pmodule -> model -> check_model_result
(* interpret concrecly and abstractly the program corresponding to the
   model (the program corresponding to the model is obtained from the
   location in the model) *)

type ce_summary

val select_model :
  ?check:bool ->
  ?reduce_config:rac_reduce_config ->
  Env.env ->
  pmodule ->
  (Call_provers.prover_answer * model) list ->
  (model * ce_summary) option
(** [select ~check ~reduce_config env pm ml] chooses a model from
   [ml]. [check] is set to false by default and indicates if
   interpretation should be used to select the model. [reduce_config]
   is set to [rac_reduce_config ()] by default and is only used if
   [check=true] *)

val model_of_ce_summary : original_model:model -> ce_summary -> model
(** [model_of_ce_summary ~original_model summary] updates
   [original_model] with information from [ce_summary] *)

(** {2 Pretty-printing results} *)

val print_check_model_result : Format.formatter -> check_model_result -> unit

val print_counterexample :
  ?check_ce:bool -> ?json:bool -> formatter -> model * ce_summary -> unit
