(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Theory
open Task

(* TODO Try to instanciate quantifiers for quantified formulas with 3 or less
   variables ? This would have a worst case complexity of m*n^3 where n is the
   number of variables that can be instantiated and m the number of quantified
   formulas with 3 or less variables. Perhaps we should only do that with the
   formulas of the local context ? At least we should avoid instantiating stuff
   from the stdlib *)

let rec simplify_fmla f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> simplify_fmla f1 @ simplify_fmla f2
  | Tbinop (Timplies, f1, f2) ->
    let conditions = simplify_fmla f1 in
    let post = simplify_fmla f2 in
    List.map
      (fun t -> List.fold_left (fun acc f -> t_implies_simp f acc) t conditions)
      post
  | Tbinop (Tiff, f1, f2) ->
    simplify_fmla (t_implies_simp f1 f2) @ simplify_fmla (t_implies_simp f2 f1)
  | Tbinop (Tor, f1, f2) ->
    simplify_fmla (t_implies_simp (t_not f1) f2)
    @ simplify_fmla (t_implies_simp (t_not f2) f1)
  | Tnot t -> (
    match t.t_node with
    | Tbinop (Tand, f1, f2) ->
      simplify_fmla (t_or (t_not_simp f1) (t_not_simp f2))
    | Tbinop (Tor, f1, f2) ->
      simplify_fmla (t_and (t_not_simp f1) (t_not_simp f2))
    | Tbinop (Timplies, f1, f2) -> simplify_fmla (t_and f1 (t_not_simp f2))
    | Tnot t2 -> simplify_fmla t2
    | _ -> [ f ])
  (* | Tquant (q, t) -> *)
  (*   let vs, trigger, t = t_open_quant t in *)
  (*   let fmlas = simplify_fmla t in *)
  (*   List.map (fun f -> t_quant_close_simp q vs trigger f) fmlas *)
  | _ -> [ f ]

let simplify d =
  match d.d_node with
  | Dprop (kind, pr, f) when kind <> Pgoal ->
    List.map
      (fun t ->
        create_prop_decl kind (create_prsymbol (Ident.id_clone pr.pr_name)) t)
      (simplify_fmla f)
  | _ -> [ d ]

let simplify_fmla_form = Trans.decl simplify None

let () =
  Trans.register_transform "simplify_fmla_form" simplify_fmla_form
    ~desc:"- Destructs@ all@ conjunctions@ and@ disjunctions."

let is_present map term =
  try
    let _ = Mterm.find term map in
    true
  with
  | Not_found -> false

let add_new_impl impls key impl =
  try
    let impl_list = Mterm.find key impls in
    Mterm.add key (impl :: impl_list) impls
  with
  | Not_found -> Mterm.add key [ impl ] impls

let add_impl f impls =
  match f.t_node with
  | Tbinop (Timplies, _, _) -> f :: impls
  | _ -> impls

let rec check_truth (truths, impls) truth =
  try
    let formulas = Mterm.find truth impls in
    let pr, _ = Mterm.find truth truths in
    let ident = pr.pr_name in
    let new_truths, new_impls =
      List.fold_left
        (fun (a, b) f ->
          match f.t_node with
          | Tbinop (Timplies, _, f2) ->
            if is_present truths f2 then
              (a, b)
            else
              (f2 :: a, add_impl f2 b)
          | _ -> assert false)
        ([], []) formulas
    in
    let impls = Mterm.remove truth impls in
    let truths =
      List.fold_left
        (fun truths t ->
          let new_id =
            create_prsymbol
              (Ident.id_derive "generated_by_eliminate_implications" ident)
          in
          Mterm.add t (new_id, Paxiom) truths)
        truths new_truths
    in
    let truths, impls = List.fold_left check_truth (truths, impls) new_truths in
    let impls =
      List.fold_left
        (fun impls t ->
          match t.t_node with
          | Tbinop (Timplies, f1, _) -> add_new_impl impls f1 t
          | _ -> assert false)
        impls new_impls
    in
    List.fold_left check_impl (truths, impls) new_impls
  with
  | Not_found -> (truths, impls)

and check_impl (truths, impls) impl =
  match impl.t_node with
  | Tbinop (Timplies, f1, f2) -> (
    try
      let pr, _ = Mterm.find f1 truths in
      let new_id =
        create_prsymbol
          (Ident.id_derive "generated_by_eliminate_implications" pr.pr_name)
      in
      let truths = Mterm.add f2 (new_id, Paxiom) truths in
      let impls = Mterm.remove f1 impls in
      let truths, impls = check_truth (truths, impls) f2 in
      match f2.t_node with
      | Tbinop (Timplies, t, _) ->
        let impls = add_new_impl impls t f2 in
        let truths, impls = check_impl (truths, impls) f2 in
        (truths, impls)
      | _ -> (truths, impls)
    with
    | Not_found -> (truths, impls))
  | _ -> assert false

let get_truths_and_impls d (truths, impls) =
  match d.d_node with
  | Dprop (kind, pr, f) when kind = Paxiom || kind = Plemma -> (
    let truths = Mterm.add f (pr, kind) truths in
    match f.t_node with
    | Tbinop (Timplies, f1, _) -> (truths, add_new_impl impls f1 f)
    | _ -> (truths, impls))
  | _ -> (truths, impls)

let rec task_fold_left fn = function
  | Some task ->
    let prev = task_fold_left fn task.task_prev in
    fn prev task.task_decl
  | None -> None

type fmla =
  | Unsupported
  | Contradiction
  | Formula of term

let get_rid_of_fmla f =
  match f.t_node with
  | Tbinop (kind, _, _) when kind = Tand || kind = Tor || kind = Tiff ->
    assert false
  | Tbinop (Timplies, _, _)
  | Ttrue ->
    true
  | _ -> false

let filter_non_arith truths acc t =
  match t.td_node with
  | Decl d -> (
    match d.d_node with
    | Dtype _
    | Ddata _
    | Dparam _
    | Dlogic _
    | Dind _ ->
      Task.add_decl acc d
    | Dprop (Pgoal, _, _) ->
      let acc =
        Mterm.fold
          (fun t (pr, _) _acc ->
            if not (get_rid_of_fmla t) then
              Task.add_decl _acc (create_prop_decl Paxiom pr t)
            else
              _acc)
          truths acc
      in
      Task.add_decl acc d
    | _ -> acc)
  | _ -> Task.add_tdecl acc t

let remove_unused_decls truths task =
  let filter_non_arith = filter_non_arith truths in
  task_fold_left filter_non_arith task

let remove_unused_decls (truths, impls) =
  let truths, _ =
    Mterm.fold_left (fun arg t _ -> check_truth arg t) (truths, impls) truths
  in
  Trans.store (remove_unused_decls truths)

let eliminate_implications =
  Trans.compose simplify_fmla_form
    (Trans.bind
       (Trans.fold_decl get_truths_and_impls (Mterm.empty, Mterm.empty))
       remove_unused_decls)

let () =
  Trans.register_transform "eliminate_implications" eliminate_implications
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
