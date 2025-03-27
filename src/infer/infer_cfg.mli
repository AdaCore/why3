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

open Domain
open Infer_why3
open Term
open Expr
open Ity

val infer_print_cfg : Debug.flag
val infer_print_ai_result : Debug.flag

module type INFERCFG = sig
  module QDom : Domain.TERM_DOMAIN

  type control_point
  type xcontrol_point = control_point * xsymbol
  type control_points = control_point * control_point * xcontrol_point list

  type domain
  type cfg
  type context = QDom.man

  val empty_context  : unit -> context
  val start_cfg      : unit -> cfg

  val cfg_size  : cfg -> int * int
  (** (number of nodes, number of hyperedges) *)

  val put_expr_in_cfg   : cfg -> context -> ?ret:vsymbol option -> expr ->
                         control_points
  val put_expr_with_pre : cfg -> context -> expr -> term list ->
                         control_points

  val eval_fixpoints : cfg -> context -> (expr * domain) list

  val domain_to_term : cfg -> context -> domain -> term

  val add_variable   : context -> pvsymbol -> unit
  (* [add_variable ctx pv] adds the variable pv to the *)
end

module Make(S:sig
  module Infer_why3 : INFERWHY3
  val    widening  : int
end)(Domain : DOMAIN): INFERCFG
