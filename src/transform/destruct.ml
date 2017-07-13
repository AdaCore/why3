(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Args_wrapper
open Generic_arg_trans_utils

(** This file contains transformations with arguments that eliminates logic
    connectors (instantiate, destruct, destruct_alg). *)

let create_constant ty =
  let fresh_name = Ident.id_fresh "x" in
  let ls = create_lsymbol fresh_name [] (Some ty) in
  (ls, create_param_decl ls)

let rec return_list list_types type_subst =
  match list_types with
  | [] -> []
  | hd :: tl ->
      create_constant (Ty.ty_inst type_subst hd) :: return_list tl type_subst

let my_ls_app_inst ls ty =
  match ls.ls_value, ty with
    | Some _, None -> raise (PredicateSymbolExpected ls)
    | None, Some _ -> raise (FunctionSymbolExpected ls)
    | Some vty, Some ty -> Ty.ty_match Ty.Mtv.empty vty ty
    | None, None -> Ty.Mtv.empty

let rec build_decls cls x =
  match cls with
  | [] -> []
  | (cs, _) :: tl ->
      let type_subst = my_ls_app_inst cs x.t_ty in
      let l = return_list cs.ls_args type_subst in
      let ht = t_equ x
           (t_app cs (List.map (fun x -> t_app_infer (fst x) []) l) x.t_ty) in
      let h = Decl.create_prsymbol (gen_ident "h") in
      let new_hyp = Decl.create_prop_decl Decl.Paxiom h ht in
      ((List.map snd l) @ [new_hyp]) :: build_decls tl x

(* This tactic acts on a term of algebraic type. It introduces one
   new goal per constructor of the type and introduce corresponding
   variables. It also introduce the equality between the term and
   its destruction in the context.
 *)
let destruct_alg (x: term) : Task.task Trans.tlist =
  let ty = x.t_ty in
  let r = ref [] in
  match ty with
  | None -> raise (Cannot_infer_type "destruct")
  | Some ty ->
    begin
      match ty.Ty.ty_node with
      | Ty.Tyvar _ -> raise (Cannot_infer_type "destruct")
      | Ty.Tyapp (ts, _) ->
        Trans.decl_l (fun d ->
          match d.d_node with
          | Ddata dls ->
              (try
                (let cls = List.assoc ts dls in
                r := build_decls cls x;
                [[d]]
                )
              with Not_found -> [[d]])
          | Dprop (Pgoal, _, _) ->
              if !r = [] then [[d]] else List.map (fun x -> x @ [d]) !r
          | _ -> [[d]]) None
    end

(* Destruct the head term of an hypothesis if it is either
   conjunction, disjunction or exists *)
let destruct pr : Task.task Trans.tlist =
  let new_decl = ref None in
  (* This transformation destructs the hypothesis pr. In case pr is an
     implication H : A -> B, the destruction creates two task (one with H
     removed and one with H : B). It also fills new_decl with A.
     The next transformation replace the first goal with A. *)
  let tr_decl =
    Trans.decl_l (fun d ->
    match d.d_node with
    | Dprop (Paxiom, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
      begin
        match ht.t_node with
        | Tbinop (Tand, t1, t2) ->
          let new_pr1 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl1 = create_prop_decl Paxiom new_pr1 t1 in
          let new_pr2 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl2 = create_prop_decl Paxiom new_pr2 t2 in
          [[new_decl1;new_decl2]]
        | Tbinop (Tor, t1, t2) ->
          let new_pr1 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl1 = create_prop_decl Paxiom new_pr1 t1 in
          let new_pr2 = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl2 = create_prop_decl Paxiom new_pr2 t2 in
          [[new_decl1];[new_decl2]]
        | Tbinop (Timplies, t1, t2) ->
          begin
            let new_pr2 = create_prsymbol (Ident.id_clone dpr.pr_name) in
            let new_decl2 = create_prop_decl Paxiom new_pr2 t2 in
            new_decl := Some t1;
            (* Creates a task with hypothesis removes (need to prove t1) and one
               with hypothesis replaced by t2 (needs to prove current goal).
               Example: "false -> false" *)
            [] :: [[new_decl2]]
          end
        | Tquant (Texists, tb) ->
          begin
            let (vsl, tr, te) = Term.t_open_quant tb in
            match vsl with
            | x :: tl ->
                let ls = create_lsymbol (Ident.id_clone x.vs_name) [] (Some x.vs_ty) in
                let tx = fs_app ls [] x.vs_ty in
                let x_decl = create_param_decl ls in
                (try
                  let part_t = t_subst_single x tx te in
                  let new_t = t_quant_close Texists tl tr part_t in
                  let new_pr = create_prsymbol (Ident.id_clone dpr.pr_name) in
                  let new_decl = create_prop_decl Paxiom new_pr new_t in
                  [[d; x_decl; new_decl]]
                with
                | Ty.TypeMismatch (ty1, ty2) ->
                    raise (Arg_trans_type ("destruct_exists", ty1, ty2)))
            | [] -> raise (Arg_trans ("destruct_exists"))
          end
        | _ -> raise (Arg_trans ("destruct"))
      end
    | _ -> [[d]]) None in
  Trans.store (fun task ->
    let goal, task = Task.task_separate_goal task in
    let new_tasks = Trans.apply tr_decl task in
    match !new_decl with
    | None ->
      (* Normal destruct case (not implication): add goal back to tasks *)
      List.map (fun task -> Task.add_tdecl task goal) new_tasks
    | Some new_decl ->
      match new_tasks with
      (* Destruct case for an implication. The first goal should be new_decl,
         the second one is unchanged. *)
      | first_task :: second_task :: [] ->
        let new_goal =
          create_prop_decl Pgoal (create_prsymbol (gen_ident "G")) new_decl in
        let first_goal = Task.add_decl first_task new_goal in
        let second_goal = Task.add_tdecl second_task goal in
        first_goal :: second_goal :: []
      | _ -> assert false)

(* from task [delta, name:forall x.A |- G,
     build the task [delta,name:forall x.A,name':A[x -> t]] |- G] *)
let instantiate (pr: Decl.prsymbol) lt =
  let r = ref [] in
  Trans.decl
    (fun d ->
      match d.d_node with
      | Dprop (pk, dpr, ht) when Ident.id_equal dpr.pr_name pr.pr_name ->
          let t_subst = subst_forall_list ht lt in
          let new_pr = create_prsymbol (Ident.id_clone dpr.pr_name) in
          let new_decl = create_prop_decl pk new_pr t_subst in
          r := [new_decl];
          [d]
      | Dprop (Pgoal, _, _) -> !r @ [d]
      | _ -> [d]) None

let () = wrap_and_register
    ~desc:"instantiate <prop> <term list> generates a new hypothesis with quantified variables of prop replaced with terms"
    "instantiate"
    (Tprsymbol (Ttermlist Ttrans)) instantiate

let () = wrap_and_register ~desc:"destruct <name> destructs the head constructor of hypothesis name"
    "destruct" (Tprsymbol Ttrans_l) destruct

let () = wrap_and_register ~desc:"destruct <name> destructs as an algebraic type"
    "destruct_alg" (Tterm Ttrans_l) destruct_alg
