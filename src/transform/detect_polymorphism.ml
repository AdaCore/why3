(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Decl
open Theory
open Task

let meta_monomorphic_types_only =
  register_meta "encoding:monomorphic_only" []
  ~desc:"Set@ when@ no@ occurence@ of@ type@ variables@ occur."

let find_in_decl d =
  match d.d_node with
  | Dtype _ts -> true (* TODO *)
  | Ddata _dl -> true (* TODO *)
  | Dparam _ls -> true (* TODO *)
  | Dlogic _dl -> true (* TODO *)
  | Dind _ind -> true (* TODO *)
  | Dprop _p ->  true (* TODO *)


let find_in_tdecl td =
  match td.td_node with
  | Decl d -> find_in_decl d
  | Use _ | Clone _ | Meta  _ -> false

let rec find_in_task task =
  match task with
  | None -> false
  | Some t -> find_in_task t.task_prev || find_in_tdecl t.task_decl

let detect_polymorphism task =
  if find_in_task task then task else
  add_meta task meta_monomorphic_types_only []
