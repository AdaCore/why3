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

exception Arg_trans of string
exception Arg_trans_decl of (string * tdecl list)
exception Arg_trans_term of (string * term)
exception Arg_trans_term2 of (string * term * term)
exception Arg_trans_term3 of (string * term * term * term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_trans_missing of (string * Svs.t)
exception Arg_bad_hypothesis of (string * term)
exception Cannot_infer_type of string
exception Unnecessary_terms of term list

let gen_ident = Ident.id_fresh

let rec t_replace_nt_na t1 t2 t =
  if t_equal_nt_na t t1 then t2 else t_map (t_replace_nt_na t1 t2) t

(* Replace all occurences of f1 by f2 in t *)
let replace_in_term = t_replace_nt_na
(* TODO be careful with attribute copy in t_map *)

let subst_quant c tq x : term =
  let (vsl, tr, te) = t_open_quant tq in
  (match vsl with
  | hdv :: tl ->
      (try
        (* TODO this should be refined in the future. In particular, we may want
           to investigate something more robust with respect to polymorphims.
        *)
        let ty_subst, subst =
          Reduction_engine.first_order_matching (Svs.add hdv Svs.empty) [Term.t_var hdv] [x]
        in
        let new_t = t_ty_subst ty_subst subst te in
        t_quant_close c tl tr new_t
      with
      | Ty.TypeMismatch (ty1, ty2) ->
          raise (Arg_trans_type ("subst_quant", ty1, ty2)))
  | [] -> failwith "subst_quant: Should not happen, please report")


let subst_quant_list quant term_quant list_term : term =
  let (vsl, triggers, te) = t_open_quant term_quant in
  (* TODO this create_mvs function should be a fold. It also can and
     should  be removed because we can use first_order_matching on list
     of terms *)
  let rec create_mvs list_term vsl acc acc_ty =
    match list_term, vsl with
    | t :: lt_tl, v :: vsl_tl ->
        let (ty_subst, _) =
          try
            Reduction_engine.first_order_matching (Svs.add v Svs.empty) [Term.t_var v] [t]
          with Reduction_engine.NoMatch _e ->
            raise (Arg_trans (Format.asprintf "cannot match %a with %a" Pretty.print_term (Term.t_var v) Pretty.print_term t))
        in
        create_mvs lt_tl vsl_tl (Mvs.add v t acc)
          (Ty.Mtv.union (fun _ _ y -> Some y) ty_subst acc_ty)
    | _ :: _, [] -> raise (Unnecessary_terms list_term)
    | [], vsl_remaining -> (acc_ty, acc), vsl_remaining
  in

  let (ty_subst, m_subst), variables_remaining =
    try
      create_mvs list_term vsl Mvs.empty Ty.Mtv.empty
    with exn -> raise (Arg_trans (Format.asprintf "subst_quant_list: exception %a" Exn_printer.exn_printer exn))
  in
  try
    let new_t = t_ty_subst ty_subst m_subst te in
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


(****************************)
(* Substitution of terms    *)
(****************************)

type term_subst = term Mterm.t

(* Same as replace but for a list of terms at once. Here, a silent
   assumption is made that any term tried to be replaced is actually a
   constant.
*)
let replace_subst (subst: term_subst) t =
  (* TODO improve efficiency of this ? *)
  Mterm.fold (fun t_from t_to acc ->
    t_replace_nt_na t_from t_to acc) subst t

let replace_decl (subst: term_subst) (d: decl) =
  decl_map (replace_subst subst) d

let replace_tdecl (subst: term_subst) (td: tdecl) =
  match td.td_node with
  | Decl d ->
      create_decl (replace_decl subst d)
  | _ -> td


(************************)
(* Explanation handling *)
(************************)

let create_goal ~expl pr t =
  let expl = Ident.create_attribute ("expl:" ^ expl) in
  let t = Term.t_attr_add expl t in
  create_prop_decl Pgoal pr t
