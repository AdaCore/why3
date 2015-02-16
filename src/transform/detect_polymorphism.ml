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
  register_meta_excl "encoding:monomorphic_only" []
  ~desc:"Set@ when@ no@ occurence@ of@ type@ variables@ occur."

exception Found

let find_in_decl d =
  match d.d_node with
  | Dtype ts ->
    Format.eprintf "======@\nFound type %a@\n" Pretty.print_ts ts;
    if ts.Ty.ts_args <> [] then
      (Format.eprintf "Type is polymorphic!@\n=======@.";
       raise Found);
    Format.eprintf "=======@."
  | Ddata _dl -> () (* TODO *)
  | Dparam _ls -> () (* TODO *)
  | Dlogic _dl -> () (* TODO *)
  | Dind _ind -> () (* TODO *)
  | Dprop _p ->  () (* TODO *)

let rec find_in_theory th = List.iter find_in_tdecl th.th_decls

and find_in_tdecl td =
  match td.td_node with
  | Decl d -> find_in_decl d
  | Use th ->
    Format.eprintf "======@\nLook up in used theory %a@." Pretty.print_th th;
    find_in_theory th
  | Clone (th,_) ->
    Format.eprintf "======@\nLook up in cloned theory %a@." Pretty.print_th th;
    find_in_theory th
  | Meta  _ -> ()

let rec find_in_task task =
  match task with
  | None -> ()
  | Some t -> find_in_task t.task_prev ; find_in_tdecl t.task_decl

let detect_polymorphism task =
  try
    find_in_task task;
    try
      let g,t = task_separate_goal task in
      let ta = add_meta t meta_monomorphic_types_only [] in
      Task.add_tdecl ta g
    with GoalNotFound ->
      add_meta task meta_monomorphic_types_only []
  with Found -> task

let () = Trans.register_transform "detect_polymorphism"
  (Trans.store detect_polymorphism)
  ~desc:"Detect if task has polymorphic types somewhere."
