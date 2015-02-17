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

let debug = Debug.register_info_flag "detect_poly"
  ~desc:"Print@ debugging@ messages@ of@ the@ 'detect_polymorphism'@ transformation."

let meta_monomorphic_types_only =
  register_meta_excl "encoding:monomorphic_only" []
  ~desc:"Set@ when@ no@ occurrences@ of@ type@ variables@ occur."

(*
let meta_has_polymorphic_types =
  register_meta_excl "encoding:polymorphic_types" []
  ~desc:"Set@ when@ occurrences@ of@ type@ variables@ occur."
*)

exception Found

open Term

let check_ts ts =
  if ts.Ty.ts_args <> [] then
    (Debug.dprintf debug "====== Type %a is polymorphic =======@."
       Pretty.print_ts ts;
     raise Found)

let check_ls ls =
  if not (ls_equal ls ps_equ) then
    try
      List.iter (fun ty -> if not (Ty.ty_closed ty) then raise Found)
        ls.ls_args
    with Found ->
      Debug.dprintf debug "====== Symbol %a is polymorphic =======@."
        Pretty.print_ls ls;
      raise Found

let check_term t =
  let s = Term.t_ty_freevars Ty.Stv.empty t in
  if not (Ty.Stv.is_empty s) then raise Found

let find_in_decl d =
  match d.d_node with
  | Dtype ts ->
    Debug.dprintf debug "@[Dtype %a@]@." Pretty.print_ts ts;
    check_ts ts
  | Ddata dl ->
    Debug.dprintf debug "@[Ddata %a@]@."
      (Pp.print_list Pp.space Pretty.print_data_decl) dl;
    List.iter (fun (ts,_) -> check_ts ts) dl;
    (* FIXME: temporary trick to activate encoding in presence
       of algebraic data types *)
    raise Found
  | Dparam ls ->
    Debug.dprintf debug "@[Dparam %a@]@." Pretty.print_ls ls;
    check_ls ls
  | Dlogic dl ->
    Debug.dprintf debug "@[Dlogic %a@]@."
      (Pp.print_list Pp.space Pretty.print_ls) (List.map fst dl);
    List.iter (fun (ls,_) -> check_ls ls) dl
    (* TODO: check also that definition bodies are monomorphic ? *)
  | Dind (_,indl) ->
    Debug.dprintf debug "@[Dind %a@]@."
      (Pp.print_list Pp.space Pretty.print_ls) (List.map fst indl);
    List.iter (fun (ls,_) -> check_ls ls) indl
    (* TODO: check also that clauses are monomorphic ? *)
  | Dprop (_,pr,t) ->
    Debug.dprintf debug "@[Dprop %a@]@." Pretty.print_pr pr;
    try check_term t
    with Found ->
      Debug.dprintf debug "====== prop is polymorphic =======@.";
      raise Found


(**)

let (*
rec find_in_theory th = List.iter find_in_tdecl th.th_decls

and
    *)
find_in_tdecl td =
  match td.td_node with
  | Decl d -> find_in_decl d
  | Use _th ->
    (* Debug.dprintf debug "Look up in used theory %a@." Pretty.print_th th; *)
    (* find_in_theory th *)
    () (* no need to traverse used theories *)
  | Clone (_th,_) ->
    (* Debug.dprintf debug "Look up in cloned theory %a@." Pretty.print_th th; *)
    (* find_in_theory th *)
    () (* no need to traverse used theories *)
  | Meta  _ -> ()

let rec find_in_task task =
  match task with
  | None -> ()
  | Some t -> find_in_task t.Task.task_prev ; find_in_tdecl t.Task.task_decl

let detect_polymorphism task =
  try
    find_in_task task;
    try
      let g,t = Task.task_separate_goal task in
      let ta = Task.add_meta t meta_monomorphic_types_only [] in
      Task.add_tdecl ta g
    with Task.GoalNotFound ->
      Task.add_meta task meta_monomorphic_types_only []
  with Found -> task

let () = Trans.register_transform "detect_polymorphism"
  (Trans.store detect_polymorphism)
  ~desc:"Detect if task has polymorphic types somewhere."


(* A variant, not satisfactory
let check_decl d =
  try
    find_in_decl d;
    [Theory.create_decl d]
  with Found ->
    [Theory.create_meta meta_has_polymorphic_types [];
     Theory.create_decl d]


let detect_polymorphism = Trans.tdecl check_decl None

let () = Trans.register_transform "detect_polymorphism"
  detect_polymorphism
  ~desc:"Detect if task has polymorphic types somewhere."

*)
