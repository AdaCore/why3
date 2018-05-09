(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Theory
open Generic_arg_trans_utils
open Args_wrapper

(* transformations "subst" and "subst_all" *)

(* This found any equality which at one side contains a single lsymbol and is
   local. It gives same output as found_eq. *)
let find_eq2 is_local_decl =
    Trans.fold_decl (fun d acc ->
      match d.d_node with
      | Dprop (k, pr, t) when k != Pgoal && is_local_decl d ->
        begin
          let acc = (match t.t_node with
          | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
            (match t1.t_node, t2.t_node with
            | Tapp (_, []), _ ->
                Some (Some pr, t1, t2)
            | _, Tapp (_, []) ->
                Some (Some pr, t2, t1)
            | _ -> acc)
          | _ -> acc) in
          acc
        end
      | Dlogic [(ls, ld)] when is_local_decl d ->
        (* Function without arguments *)
        let vl, e = open_ls_defn ld in
        if vl = [] then
          Some (None, t_app_infer ls [], e)
        else
          acc
      | _ -> acc) None

let subst_eq found_eq =
  match found_eq with
    | None -> raise (Arg_trans "subst_eq")
    | Some (Some pr_eq, t1, t2) ->
      begin
        Trans.decl (fun d ->
          match d.d_node with
          (* Remove equality over which we subst *)
          | Dprop (_k, pr, _t) when pr_equal pr pr_eq  ->
            []
          (* Replace in all hypothesis *)
          | Dprop (kind, pr, t) ->
            [create_prop_decl kind pr (t_replace t1 t2 t)]
          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
      end
    | Some (None, t1, t2) ->
      begin
         Trans.decl (fun d ->
           match d.d_node with
           | Dlogic [(ls, _ld)] when try (t1 = Term.t_app_infer ls []) with _ -> false ->
              []
           (* Replace in all hypothesis *)
           | Dprop (kind, pr, t) ->
             [create_prop_decl kind pr (t_replace t1 t2 t)]

          | Dlogic ldecl_list ->
            let ldecl_list =
              List.map (fun (ls, ls_def) ->
                let (vl, t) = open_ls_defn ls_def in
                make_ls_defn ls vl (t_replace t1 t2 t)) ldecl_list
            in
            [create_logic_decl ldecl_list]

          (* TODO unbelievably complex for something that simple... *)
          | Dind ((is: ind_sign), (ind_list: ind_decl list)) ->
            let ind_list: ind_decl list =
              List.map (fun ((ls: lsymbol), (idl: (prsymbol * term) list)) ->
                let idl = List.map (fun (pr, t) -> (pr, t_replace t1 t2 t)) idl in
                (ls, idl)) ind_list
            in
            [create_ind_decl is ind_list]

          | Dtype _ | Ddata _ | Dparam _ -> [d]) None
       end

let subst_eq_list (found_eq_list, _) =
  List.fold_left (fun acc_tr found_eq ->
    Trans.compose (subst_eq found_eq) acc_tr) Trans.identity found_eq_list

let subst_all (is_local_decl: Decl.decl -> bool) =
   Trans.bind (find_eq2 is_local_decl) subst_eq

let return_local_decl task =
  let decl_list = get_local_task task in
  let is_local_decl d = List.exists (fun x -> Decl.d_equal d x) decl_list in
  is_local_decl

let return_local_decl = Trans.store return_local_decl

let subst_all = Trans.bind return_local_decl subst_all

let rec repeat f task =
  try
    let new_task = Trans.apply f task in
    (* TODO this is probably expansive. Use a checksum or an integer ? *)
    if Task.task_equal new_task task then
      raise Exit
    else
      repeat f new_task
  with
  | _ -> task

let repeat f = Trans.store (repeat f)

let subst_all = repeat subst_all

(* TODO implement subst_all as repeat subst ??? *)

let () =
  wrap_and_register ~desc:"substitute all ident equalities and remove them"
    "subst_all"
    (Ttrans) subst_all



(*********)
(* Subst *)
(*********)

(* Creation of as structure that associates the replacement of terms as a
   function of the
*)
type constant_subst_defining =
  | Cls of lsymbol
  | Cpr of prsymbol

module Csd = Stdlib.MakeMSHW (struct
  type t = constant_subst_defining
  let tag (c: t) = match c with
  | Cls ls -> ls.ls_name.Ident.id_tag
  | Cpr pr -> pr.pr_name.Ident.id_tag
end)

module Mcsd = Csd.M

(* We find the hypotheses that have a substitution equality for elements of the
   to_subst list. We check that we never take more than one equality per
   lsymbol to substitute.
*)
let find_eq_aux (to_subst: Term.lsymbol list) =
  Trans.fold_decl (fun d (acc, used) ->
    match d.d_node with
    | Dprop (k, pr, t) when k != Pgoal ->
        let acc, used = (match t.t_node with
        | Tapp (ls, [t1; t2]) when ls_equal ls ps_equ ->
          (* Allow to rewrite from the right *)
          begin
            match t1.t_node, t2.t_node with
            | Tapp (ls, []), _ when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t1, t2) acc, ls :: used
            | _, Tapp (ls, []) when List.exists (ls_equal ls) to_subst &&
                                    (* Check ls is not already taken *)
                                    not (List.exists (ls_equal ls) used) ->
                Mcsd.add (Cpr pr) (t2, t1) acc, ls :: used
            | _ -> acc, used
          end
        | _ -> acc, used) in
        acc, used
    | Dlogic [(ls, ld)] when List.exists (ls_equal ls) to_subst &&
                             (* Check ls is not already taken *)
                             not (List.exists (ls_equal ls) used) ->
      (* Function without arguments *)
      let vl, e = open_ls_defn ld in
      if vl = [] then
        Mcsd.add (Cls ls) (t_app_infer ls [], e) acc, ls :: used
      else
        acc, used
    | _ -> acc, used) (Mcsd.empty,[])

(* Wrap-around function to parse lsymbol instead of terms *)
let find_eq to_subst =
  let to_subst = (List.map
     (fun t -> match t.t_node with
     | Tapp (ls, []) -> ls
     | _ -> raise (Arg_trans "subst_eq")) to_subst)
  in
  find_eq_aux to_subst

(* This produce an ordered list of tdecl which is the original task minus the
   hypotheses/constants that were identified for substitution.
   This shall be done on tdecl.
*)
let remove_hyp_and_constants (replacing_hyps, used_ls) =
  (* The task_fold on tdecl is necessary as we *need* all the tdecl (in
     particular to identify local decls).
  *)
  Task.task_fold (fun (subst, list_tdecl) td ->
    match td.td_node with
    | Decl d ->
      begin
        match d.d_node with
        | Dprop (kind, pr, _t) when kind != Pgoal &&
                                    Mcsd.mem (Cpr pr) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cpr pr) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dlogic [ls, _] when Mcsd.mem (Cls ls) replacing_hyps ->
          let from_t, to_t = Mcsd.find (Cls ls) replacing_hyps in
          (* TODO find a way to be more efficient than this *)
          let to_t = Generic_arg_trans_utils.replace_subst subst to_t in
          Mterm.add from_t to_t subst, list_tdecl
        | Dparam ls when List.exists (ls_equal ls) used_ls ->
          subst, list_tdecl
        | _ ->
          subst, (replace_tdecl subst td :: list_tdecl)
      end
    | _ -> (subst, td :: list_tdecl)
    ) (Mterm.empty, [])

let remove_hyp_and_constants (replacing_hyps, used_ls) =
  Trans.store (remove_hyp_and_constants (replacing_hyps, used_ls))

let is_goal td =
  match td.td_node with
  | Decl d ->
      begin
        match d.d_node with
        | Dprop (Pgoal, _, _) -> true
        | _ -> false
      end
  | _ -> false

(* Use the list of tdecl that should be able to be readded into a task if there
   was sufficiently few things that were removed to the task.
   To do this, we use Task.add_tdecl (because we think its the safest).
   Note that we also try to keep the order of the declarations (because
   usability). So, each time we add a new declaration, we try to add all the
   transformations that failed (supposedly because they use a variable declared
   after it).
*)
let readd_decls (list_decls, subst: tdecl list * _) =
  List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
    let d = replace_tdecl subst d in
    let task_uc, list_to_add =
      List.fold_left (fun (task_uc, list_to_add) (d: tdecl) ->
        try
          let new_task_uc = Task.add_tdecl task_uc d in
          new_task_uc, list_to_add
        with
          (* TODO find all possible exceptions here *)
          _ -> task_uc, d :: list_to_add)
        (task_uc, []) list_to_add
    in
    (* We always need to add the goal last *)
    if is_goal d then
      if list_to_add != [] then
        raise (Arg_trans_decl ("subst_eq", list_to_add))
      else
        try
          (Task.add_tdecl task_uc d, [])
        with
        (* TODO find all possible exceptions here *)
          _ -> raise (Arg_trans_decl ("subst_eq", [d]))
    else
      try
        (Task.add_tdecl task_uc d, List.rev list_to_add)
      with
        _ -> (task_uc, List.rev (d :: list_to_add)))
    (None, []) list_decls

let readd_decls (subst, list_decls) =
  let (task, _l) = readd_decls (list_decls, subst) in
  Trans.return task

let find args = Trans.bind (find_eq args) remove_hyp_and_constants

let subst args = Trans.bind (find args) readd_decls

let () = wrap_and_register ~desc:"remove a literal using an equality on it"
    "subst"
    (Ttermlist Ttrans) subst
