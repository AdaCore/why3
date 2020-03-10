(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

#13 "src/mlw/infer_loop_enable.ml"
open Ident
open Theory
open Ity
open Expr

let infer_flag =
  Debug.register_flag "infer-loop" ~desc:"Infer loop invariants"

let attrs_has_infer attrs =
  Sattr.exists (fun a -> Strings.has_prefix "infer" a.attr_string) attrs

let infer_loops env tkn mkn e cty =
  let module AI = Ai_cfg.Make (struct
    let env = env
    let th_known = tkn
    let mod_known = mkn
    let widening = 3
    module D = Domain.Polyhedra end) in
  let preconditions = cty.cty_pre in
  let cfg = AI.start_cfg () in
  let context = AI.empty_context () in
  List.iter (AI.add_variable cfg context) cty.cty_args;
  if Debug.test_flag Uf_domain.infer_debug then
    Format.printf "%a@." Expr.print_expr e;
  ignore (AI.put_expr_with_pre cfg context e preconditions);
  (* will hold the different file offsets (useful when writing
     multiple invariants) *)
  let fixp = AI.eval_fixpoints cfg context in
  let domain2term (e,d) =
    let expl = "expl:infer-loop" in
    let t    = AI.domain_to_term cfg context d in
    let t    = Term.t_attr_add (Ident.create_attribute expl) t in
    if Debug.test_flag Uf_domain.infer_debug then
      Pretty.print_term Format.std_formatter t;
    (e,t) in
  List.map domain2term fixp

let infer_loops attrs env tkn mkn e cty =
  if Debug.test_flag infer_flag || attrs_has_infer attrs  then
    infer_loops env tkn mkn e cty
  else []
