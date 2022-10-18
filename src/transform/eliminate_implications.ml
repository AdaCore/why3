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
open Ty
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
  | _ -> [ f ]

let simplify d =
  match d.d_node with
  | Dprop (kind, pr, f) ->
    List.map (fun t -> create_prop_decl kind pr t) (simplify_fmla f)
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

let rec get_fmlas f =
  match f.t_node with
  | Tbinop (Timplies, f1, f2) -> ([], [ f ])
  | _ -> ([], [])

let add_impl f impls =
  match f.t_node with
  | Tbinop (Timplies, _, _) -> f :: impls
  | _ -> impls

let rec check_truth (truths, impls) truth =
  try
    let formulas = Mterm.find truth impls in
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
      List.fold_left (fun truths t -> Mterm.add t () truths) truths new_truths
    in
    let truths, impls = List.fold_left check_truth (truths, impls) new_truths in
    let impls =
      List.fold_left
        (fun impls t ->
          match t.t_node with
          | Tbinop (Timplies, f1, f2) -> Mterm.add f1 t impls
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
      let () = Mterm.find f1 truths in
      let truths = Mterm.add f2 () truths in
      let impls = Mterm.remove f1 impls in
      let truths, impls = check_truth (truths, impls) f2 in
      match f2.t_node with
      | Tbinop (Timplies, _, _) ->
        let truths, impls = check_impl (truths, impls) f2 in
        let impls = Mterm.add f1 t impls in
        (truths, impls)
      | _ -> (truths, impls)
    with
    | Not_found -> (truths, impls))
  | _ -> assert false

let get_truths_and_impls d (truths, impls) =
  match d.d_node with
  | Dprop (Paxiom, pr, f)
  | Dprop (Plemma, pr, f) ->
    let truths = Mterm.add f () truths in
    let new_truths, new_impls = get_fmlas f in
    let truths =
      List.fold_left (fun truths t -> Mterm.add t () truths) truths new_truths
    in
    let impls =
      List.fold_left
        (fun impls t ->
          match t.t_node with
          | Tbinop (Timplies, f1, f2) -> Mterm.add f1 t impls
          | _ -> assert false)
        impls new_impls
    in
    (truths, impls)
  | _ -> (truths, impls)

type fmla =
  | Unsupported
  | Tautology
  | Contradiction
  | Formula of term

let rec get_fmla symbols f =
  let get = get_fmla symbols in
  match f.t_node with
  | Tbinop (Tor, f1, f2) -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Tautology
    | Contradiction -> get f2
    | Formula f1 -> (
      match get f2 with
      | Unsupported -> Unsupported
      | Tautology -> Tautology
      | Contradiction -> Formula f1
      | Formula f2 -> Formula (t_or f1 f2)))
  | Ttrue -> Tautology
  | Tfalse -> Contradiction
  | Tnot f1 -> (
    match get f1 with
    | Unsupported -> Unsupported
    | Tautology -> Contradiction
    | Contradiction -> Tautology
    | Formula f -> Formula (t_not f))
  | Tapp (ls, [ t1; _ ]) ->
    if ls_equal ls ps_equ then
      match t1.t_ty with
      | Some ty ->
        if ty_equal ty ty_int || ty_equal ty ty_real then
          Formula f
        else
          Unsupported
      | None -> Formula f
    else if List.exists (fun _ls -> ls_equal ls _ls) symbols then
      Formula f
    else
      Unsupported
  | Tquant (Tforall, t) -> (
    let vs, trigger, t = t_open_quant t in
    match get t with
    | Formula f -> Formula (t_forall_close_simp vs trigger f)
    | _ -> Unsupported)
  | _ -> Unsupported

let rec task_fold_left fn = function
  | Some task ->
    let prev = task_fold_left fn task.task_prev in
    fn prev task.task_decl
  | None -> None

let filter_non_arith symbols truths acc t =
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
      let get_fmla = get_fmla symbols in
      let acc =
        Mterm.fold_left
          (fun _acc t _ ->
            match get_fmla t with
            | Formula _
            | Contradiction ->
              Task.add_decl _acc
                (create_prop_decl Paxiom
                   (create_prsymbol (Ident.id_fresh "dummy"))
                   t)
            | _ -> _acc)
          acc truths
      in
      Task.add_decl acc d
    | _ -> acc)
  | _ -> Task.add_tdecl acc t

let remove_unused_decls truths task =
  let filter_non_arith = filter_non_arith symbols truths in
  task_fold_left filter_non_arith task

let remove_unused_decls (truths, impls) =
  let truths, _ =
    Mterm.fold_left (fun arg t () -> check_truth arg t) (truths, impls) truths
  in
  Trans.store (remove_unused_decls symbols truths)

let eliminate_implications =
  Trans.bind
    (Trans.fold_decl get_truths_and_impls (Mterm.empty, Mterm.empty))
    remove_unused_decls

let () =
  Trans.register_transform "eliminate_implications" eliminate_implications
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
