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

open Format
open Pinterp
open Model_parser
open Pmodule

val debug_check_ce : Debug.flag

type check_model_result

val check_model :
  rac_reduce_config ->
  Env.env ->
  pmodule ->
  model ->
  check_model_result

type ce_summary

val select_model :
  ?check:bool ->
  ?reduce_config:rac_reduce_config ->
  Env.env ->
  pmodule ->
  (Call_provers.prover_answer * model) list ->
  (model * ce_summary) option

val model_of_ce_summary : original_model:model -> ce_summary -> model

val print_counterexample :
  ?check_ce:bool -> ?json:bool -> formatter -> model * ce_summary -> unit

val print_check_model_result : Format.formatter -> check_model_result -> unit
