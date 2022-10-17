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

(* TODO Remove Tor ? *)
(* Remove all that is not an equality/inequality or quantified stuff. Also
   remove Timplies, Tiff, Tand. We could still throw away quantified assertions
   that could be used on implications if instanciated, but its probably too
   costly to use them. *)

let rec get_fmlas f =
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> (
    let new_truths, new_impls = ([ f1; f2 ], []) in
    let new_truths, new_impls =
      match f1.t_node with
      | Tbinop (Timplies, _, _)
      | Tbinop (Tiff, _, _) ->
        let truths, impls = get_fmlas f1 in
        (new_truths @ truths, new_impls @ impls)
      | _ -> (new_truths, new_impls)
    in
    match f2.t_node with
    | Tbinop (Timplies, _, _)
    | Tbinop (Tiff, _, _) ->
      let truths, impls = get_fmlas f2 in
      (new_truths @ truths, new_impls @ impls)
    | _ -> (new_truths, new_impls))
  | Tbinop (Timplies, f1, f2) -> ([], [ f ])
  | Tbinop (Tiff, f1, f2) ->
    ([ t_implies f1 f2; t_implies f2 f1 ], [ t_implies f1 f2; t_implies f2 f1 ])
  | _ -> ([], [])

let rec check_truth (truths, impls) truth =
  try
    let f =
      match (Mterm.find truth impls).t_node with
      | Tbinop (Timplies, f1, f2) -> f2
      | _ -> assert false
    in
    let truths = Mterm.add f () truths in
    let impls = Mterm.remove truth impls in
    let new_truths, new_impls = get_fmlas f in
    let new_truths = [ f ] @ new_truths in
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
      let new_truths, new_impls = get_fmlas f2 in
      let new_truths = [ f2 ] @ new_truths in
      let truths =
        List.fold_left (fun truths t -> Mterm.add t () truths) truths new_truths
      in
      let truths, impls =
        List.fold_left check_truth (truths, impls) new_truths
      in
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

let remove_unused_decls symbols truths task =
  let filter_non_arith = filter_non_arith symbols truths in
  task_fold_left filter_non_arith task

let remove_unused_decls_ symbols (truths, impls) =
  let truths, _ =
    Mterm.fold_left (fun arg t () -> check_truth arg t) (truths, impls) truths
  in
  Trans.store (remove_unused_decls symbols truths)

let remove_non_arith symbols =
  Trans.bind
    (Trans.fold_decl get_truths_and_impls (Mterm.empty, Mterm.empty))
    (remove_unused_decls_ symbols)

let keep_only_arithmetic env =
  let symbol_names =
    [
      Ident.op_infix "<";
      Ident.op_infix "<=";
      Ident.op_infix ">";
      Ident.op_infix ">=";
    ]
  in
  let int = Env.read_theory env [ "int" ] "Int" in
  let int_symbols =
    List.map (fun name -> ns_find_ls int.th_export [ name ]) symbol_names
  in
  let real = Env.read_theory env [ "real" ] "Real" in
  let real_symbols =
    List.map (fun name -> ns_find_ls real.th_export [ name ]) symbol_names
  in
  let symbols = int_symbols @ real_symbols in
  Trans.compose
    (Trans.lookup_transform "inline_trivial" env)
    (remove_non_arith symbols)

let () =
  Trans.register_env_transform "keep_only_arithmetic" keep_only_arithmetic
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
