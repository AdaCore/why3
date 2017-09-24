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

exception Arg_trans of string
exception Arg_trans_term of (string * term * term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_bad_hypothesis of (string * term)
exception Cannot_infer_type of string
exception Unnecessary_terms of term list

let gen_ident = Ident.id_fresh

(* Replace all occurences of f1 by f2 in t *)
let replace_in_term = Term.t_replace
(* TODO be careful with label copy in t_map *)

let subst_quant c tq x : term =
  let (vsl, tr, te) = t_open_quant tq in
  (match vsl with
  | hdv :: tl ->
      (try
        let new_t = t_subst_single hdv x te in
        t_quant_close c tl tr new_t
      with
      | Ty.TypeMismatch (ty1, ty2) ->
          raise (Arg_trans_type ("subst_quant", ty1, ty2)))
  | [] -> failwith "subst_quant: Should not happen, please report")


let subst_quant_list quant term_quant list_term : term =
  let (vsl, triggers, te) = t_open_quant term_quant in
  let rec create_mvs list_term vsl acc =
    match list_term, vsl with
    | t :: lt_tl, v :: vsl_tl ->
        create_mvs lt_tl vsl_tl (Mvs.add v t acc)
    | _ :: _, [] -> raise (Unnecessary_terms list_term)
    | [], vsl_remaining -> acc, vsl_remaining
  in
  let m_subst, variables_remaining = create_mvs list_term vsl Mvs.empty in
  try
    let new_t = t_subst m_subst te in
    t_quant_close quant variables_remaining triggers new_t
  with
  | Ty.TypeMismatch (ty1, ty2) ->
      raise (Arg_trans_type ("subst_quant_list", ty1, ty2))

(* Transform the term (exists v, f) into f[x/v] *)
let subst_exist t x =
  match t.t_node with
  | Tquant (Texists, tq) ->
      subst_quant Texists tq x
  | _ -> raise (Arg_trans "subst_exist")

(* Transform the term (forall v, f) into f[x/v] *)
let subst_forall t x =
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant Tforall tq x
  | _ -> raise (Arg_trans "subst_forall")


(* Squash forall x y. forall z into forall x y z. Squashing also removes
   triggers.
*)
let squash_forall t =
  let rec squash_forall_aux vl t =
    match t.t_node with
    | Tquant (Tforall, tq) ->
      let (new_v, _, t) = t_open_quant tq in
      squash_forall_aux (vl @ new_v) t
    | _ -> t_forall (t_close_quant vl [] t)
  in
  squash_forall_aux [] t

(* Same as subst_forall but l is a list of term *)
let subst_forall_list t l =
  let t = squash_forall t in
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant_list Tforall tq l
  | _ -> raise (Arg_trans "subst_forall_list")

(* Returns the list of local declarations as a transformation *)
let get_local =
  Trans.store (fun task ->
    let local_decls =
      let ut = Task.used_symbols (Task.used_theories task) in
      Task.local_decls task ut in
    local_decls)

let get_local_task task =
  let ut = Task.used_symbols (Task.used_theories task) in
  Task.local_decls task ut


let sort local_decls =
  let l = ref [] in
  Trans.decl
    (fun d ->
      match d.d_node with
      | _ when not (List.exists (fun x -> Decl.d_equal x d) local_decls) ->
          [d]
      | Dprop (Paxiom, _, _)
      | Dprop (Plemma, _, _)
      | Dprop (Pskip, _, _) ->
          (* This goes in the second group *)
          l := !l @ [d];
          []
      | Dprop (Pgoal, _, _) ->
          (* Last element, we concatenate the list of postponed elements *)
          !l @ [d]
      | _ -> [d]) None

(* TODO is sort really needed ? It looked like it was for subst in some example
   where I wanted to subst the definition of a logic constant into an equality
   and it would fail because the equality is defined before the logic definition.
   This may be solved by current implementation of subst: to be tested.
*)
let sort =
  Trans.bind get_local sort
