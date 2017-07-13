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


(* Same as subst_forall but l is a list of term *)
let subst_forall_list t l =
  match t.t_node with
  | Tquant (Tforall, tq) ->
      subst_quant_list Tforall tq l
  | _ -> raise (Arg_trans "subst_forall_list")
