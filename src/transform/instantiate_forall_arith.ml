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

open Task
open Term
open Decl
open Ty

(* We use maps instead of lists to avoid having the same element twice *)
type arith_terms = {
  int_terms : unit Mterm.t;
  real_terms : unit Mterm.t;
}

let rec instantiate f terms =
  match f.t_node with
  | Tbinop (Tand, f1, f2) -> instantiate f1 terms @ instantiate f2 terms
  | Tbinop (Tor, _, _) ->
    [] (* This can be huge, do we want to instanciate here ? *)
  | Tbinop (Timplies, f1, f2) ->
    let fmlas = instantiate f2 terms in
    List.map (fun f -> t_implies_simp f1 f) fmlas
  | Tbinop (Tiff, f1, f2) ->
    instantiate (t_implies_simp f1 f2) terms
    @ instantiate (t_implies_simp f2 f1) terms
  | Tnot f1 ->
    let fmlas = instantiate f1 terms in
    List.map (fun f -> t_not_simp f) fmlas
  | Tquant (Tforall, t) ->
    let vs, _, t = t_open_quant t in
    let fmlas = t :: instantiate t terms in
    List.fold_left
      (fun acc vs ->
        List.fold_left
          (fun _acc t ->
            let terms =
              if ty_equal vs.vs_ty ty_int then
                terms.int_terms
              else
                terms.real_terms
            in
            Mterm.fold_left
              (fun __acc term () -> t_subst_single vs term t :: __acc)
              [] terms)
          [] acc)
      fmlas vs
  | _ -> []

let instantiate_fmlas arith_terms =
  Trans.store (fun task ->
      let goal, task = task_separate_goal task in
      let decls = task_decls task in
      let task =
        List.fold_left
          (fun task d ->
            match d.d_node with
            | Dprop (kind, pr, f) ->
              let fmlas = instantiate f arith_terms in
              List.fold_left
                (fun task fmla ->
                  add_prop_decl task kind
                    (create_prsymbol
                       (Ident.id_derive "generated_by_instantiate_forall_arith"
                          pr.pr_name))
                    fmla)
                task fmlas
            | _ -> task)
          task decls
      in
      add_tdecl task goal)

let add_term t ty terms =
  if ty_equal ty ty_int then
    {
      int_terms = Mterm.add t () terms.int_terms;
      real_terms = terms.real_terms;
    }
  else if ty_equal ty ty_real then
    {
      int_terms = terms.int_terms;
      real_terms = Mterm.add t () terms.real_terms;
    }
  else
    assert false

let rec get_arith_terms banned t arith_terms =
  let get_arith = get_arith_terms banned in
  match t.t_node with
  | Tbinop (_, t1, t2) ->
    let arith_terms, _ = get_arith t1 arith_terms in
    let arith_terms, _ = get_arith t2 arith_terms in
    (arith_terms, false)
  | Tnot t ->
    let arith_terms, _ = get_arith t arith_terms in
    (arith_terms, false)
  | Tapp (ls, terms) -> (
    let arith_terms, is_ok =
      List.fold_left
        (fun (arith_terms, is_ok) t ->
          let arith_terms, is_ok' = get_arith t arith_terms in
          (arith_terms, is_ok && is_ok'))
        (arith_terms, true) terms
    in
    match ls.ls_value with
    | Some ty when is_ok && (ty_equal ty ty_int || ty_equal ty ty_real) ->
      (add_term t ty arith_terms, true)
    | _ -> (arith_terms, is_ok))
  | Tquant (_, t) ->
    let vs, _, t = t_open_quant t in
    let banned = banned @ vs in
    let arith_terms, _ = get_arith_terms banned t arith_terms in
    (arith_terms, false)
  | Tconst c -> (
    match c with
    | ConstInt _ -> (add_term t ty_int arith_terms, true)
    | ConstReal _ -> (add_term t ty_real arith_terms, true)
    | _ -> (arith_terms, true))
  | Tvar vs
    when (ty_equal vs.vs_ty ty_int || ty_equal vs.vs_ty ty_real)
         && not (List.exists (fun _vs -> vs_equal vs _vs) banned) ->
    (add_term t vs.vs_ty arith_terms, true)
  | _ -> (arith_terms, false)

let get_terms_and_quantified_fmlas d arith_terms =
  match d.d_node with
  | Dprop (_, _, f) ->
    let arith_terms, _ = get_arith_terms [] f arith_terms in
    arith_terms
  | _ -> arith_terms

let instantiate_forall_arith =
  Trans.bind
    (Trans.fold_decl get_terms_and_quantified_fmlas
       { int_terms = Mterm.empty; real_terms = Mterm.empty })
    instantiate_fmlas

let () =
  Trans.register_transform "instantiate_forall_arith" instantiate_forall_arith
    ~desc:
      "This@ transformation@ tries@ to@ instantiate@ universally@ quantified@ \
       formulas@ on@ arithmetic@ terms."
