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

(* TODO: Remove all that is not an equality/inequality or quantified stuff. Also
   remove Timplies, Tiff, Tand. Also rem We could still throw away quantified
   assertions that could be used on implications if instanciated, but its
   probably too costly to use them. *)

(* type fmla = *)
(*   | Unsupported *)
(*   | Tautology *)
(*   | Contradiction *)
(*   | Formula of term *)

(* let rec check_impl_instanciation truths passed_impls impls = *)
(*   match impls with *)
(*   | impl :: tl -> ( *)
(*     match impl with *)
(*     | Tbinop (Timplies, t1, t2) -> ( *)
(*       match Mterm.find t1 truths with *)
(* | _ -> let truths = Mterm.add t2 () truths in let truths =
   check_impl_instanciation truths passed_impls *)
(* | Not_found -> check_impl_instanciation truths (passed_impls :: impl) tl) *)
(*     | _ -> assert false) *)
(*   | [] -> truths *)

(* let rec get_fmla symbols f = *)
(*   let get = get_fmla symbols in *)
(*   match f.t_node with *)
(*   | Tbinop (Tand, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported *)
(*     | Tautology -> *)
(*       get f2 *)
(*     | Contradiction -> Contradiction *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported *)
(*       | Tautology -> *)
(*         Formula f1 *)
(*       | Contradiction -> Contradiction *)
(*       | Formula f2 -> Formula (t_and f1 f2))) *)
(*   | Tbinop (Tor, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported -> Unsupported *)
(*     | Tautology -> Tautology *)
(*     | Contradiction -> get f2 *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported -> Unsupported *)
(*       | Tautology -> Tautology *)
(*       | Contradiction -> Formula f1 *)
(*       | Formula f2 -> Formula (t_or f1 f2))) *)
(*   | Tbinop (Timplies, f1, f2) -> ( *)
(*     match get f1 with *)
(*     | Unsupported *)
(*     | Contradiction -> *)
(*       Unsupported *)
(*     | Tautology -> get f2 *)
(*     | Formula f1 -> ( *)
(*       match get f2 with *)
(*       | Unsupported -> Unsupported *)
(*       | Tautology -> Tautology *)
(*       | Contradiction -> Formula (t_implies f1 t_false) *)
(*       | Formula f2 -> Formula (t_implies f1 f2))) *)
(*   (* TODO: Tbinop tiff ? *) *)
(*   | Ttrue -> Tautology *)
(*   | Tfalse -> Contradiction *)
(*   | Tnot f1 -> ( *)
(*     match get f1 with *)
(*     | Unsupported -> Unsupported *)
(*     | Tautology -> Contradiction *)
(*     | Contradiction -> Tautology *)
(*     | Formula f -> Formula (t_not f)) *)
(*   | Tapp (ls, [ t1; _ ]) -> *)
(*     if ls_equal ls ps_equ then *)
(*       match t1.t_ty with *)
(*       | Some ty -> *)
(*         if ty_equal ty ty_int || ty_equal ty ty_real then *)
(*           Formula f *)
(*         else *)
(*           Unsupported *)
(*       | None -> Formula f *)
(*     else if List.exists (fun _ls -> ls_equal ls _ls) symbols then *)
(*       Formula f *)
(*     else *)
(*       Unsupported *)
(*   | Tquant (Tforall, t) -> ( *)
(*     let vs, trigger, t = t_open_quant t in *)
(*     match get t with *)
(*     | Formula f -> Formula (t_forall_close_simp vs trigger f) *)
(*     | _ -> Unsupported) *)
(*   | _ -> Unsupported *)

(* TODO: Forall instanciation *)
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
    let f = Mterm.find truth impls in
    let impls = Mterm.remove truth impls in
    let new_truths, new_impls = get_fmlas f in
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
      let impls = Mterm.remove f1 impls in
      let new_truths, new_impls = get_fmlas f2 in
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

let get_truths_and_impls (truths, impls) d =
  match d.d_node with
  | Dprop (Paxiom, pr, f)
  | Dprop (Plemma, pr, f) ->
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
  Trans.bind Trans.identity (fun task ->
      let _, task = task_separate_goal task in
      let goal_fmla = task_goal_fmla task in
      match goal_fmla.t_node with
      | Tapp (ls, [ t1; t2 ]) ->
        if List.exists (fun _ls -> ls_equal ls _ls) (symbols @ [ ps_equ ]) then
          let decls = task_decls task in
          let truths, impls =
            List.fold_left get_truths_and_impls (Mterm.empty, Mterm.empty) decls
          in
          assert false
        else
          failwith "Unsupported goal"
      | _ -> failwith "Unsupported goal")

let () =
  Trans.register_env_transform "keep_only_arithmetic" keep_only_arithmetic
    ~desc:
      "Only@ keep@ declarations@ of@ integer@ and@ real@ variables,@ also@ \
       only@ keep@ assertions@ about@ inequalities@ or@ equalites@ between@ \
       integers@ and@ reals."
