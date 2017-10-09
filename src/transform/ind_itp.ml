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

open Decl
open Term
open Generic_arg_trans_utils
open Args_wrapper

(** This file contains the transformation with arguments 'induction on integer' *)

let is_good_type t ty =
  try (Term.t_ty_check t (Some ty); true) with
  | _ -> false

(* Reverts a declaration d to a goal g *)
let revert g d =
  match d.d_node with
  | Dtype _ -> raise (Arg_trans "revert: cannot revert type")
  | Ddata _ -> raise (Arg_trans "revert: cannot revert type")
  | Dparam ls ->
    (try
      let new_ident = Ident.id_fresh ls.ls_name.Ident.id_string in
      let new_var = Term.create_vsymbol new_ident (Opt.get ls.Term.ls_value) in
      let g = t_replace (t_app_infer ls []) (t_var new_var) g in
      t_forall_close [new_var] [] g
    with
    | _ -> raise (Arg_trans ("revert: cannot revert:" ^ ls.ls_name.Ident.id_string)))
  (* TODO extend this *)
  | Dlogic _ ->
    raise (Arg_trans "revert: cannot revert logic decls")
  | Dind _ ->
    raise (Arg_trans "revert: cannot revert induction decls")
  | Dprop (k, _pr, t) when k <> Pgoal ->
    Term.t_implies t g
  | Dprop (Pgoal, _, _) -> raise (Arg_trans "revert: cannot revert goal")
  | _ -> raise (Arg_trans "revert: please report")


(* Takes a list of prop l and a goal g and reverts the list
   of prop to the goal g *)
let revert_list (l: decl list) g =
  List.fold_left revert g l

(* From task [delta, x: int, delta'(x) |- G(x)], variable x and term bound, builds the tasks:
   [delta, x: int, x <= bound, delta'(x) |- G(x)] and
   [delta, x: int, x >= bound, (delta'(x) -> G(x)), delta'(x+1) |- G(x+1)]
*)
let induction x bound env =
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let plus_int = Theory.ns_find_ls th.Theory.th_export ["infix +"] in
  let one_int =
    Term.t_const (Number.ConstInt (Number.int_const_of_int 1)) Ty.ty_int in
  (* bound is optional and set to 0 if not given *)
  let bound =
    match bound with
    | None -> Term.t_const (Number.ConstInt (Number.int_const_of_int 0)) Ty.ty_int
    | Some bound -> bound
  in

  if (not (is_good_type x Ty.ty_int) || not (is_good_type bound Ty.ty_int)) then
    raise (Arg_trans "induction")
  else
    let lsx = match x.t_node with
    | Tvar lsx -> lsx.vs_name
    | Tapp (lsx, []) -> lsx.ls_name
    | _ -> raise (Arg_trans "induction") in

  let le_bound = Trans.decl (fun d -> match d.d_node with
    | Dprop (Pgoal, _pr, _t) ->
        let nt = Term.t_app_infer le_int [x; bound] in
        let pr = create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "Init")) nt in
        [pr; d]
    | _ -> [d]) None in

  let x_is_passed = ref false in
  let delta_x = ref [] in
  let ge_bound =
    Trans.decl (fun d -> match d.d_node with
    | Dparam ls when (Ident.id_equal lsx ls.ls_name) ->
        (x_is_passed := true; [d])
    | Dprop (Pgoal, _pr, t) ->
        if not (!x_is_passed) then
          raise (Arg_trans "induction")
        else
          let t_delta_x = revert_list !delta_x t in
          let x_ge_bound_t = t_app_infer le_int [bound; x] in
          let x_ge_bound =
            create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "Init")) x_ge_bound_t in
          let rec_pr = create_prsymbol (gen_ident "Hrec") in
          let new_pr = create_prsymbol (gen_ident "G") in
          let new_goal = create_prop_decl Pgoal new_pr
              (replace_in_term x (t_app_infer plus_int [x; one_int]) t) in
          [x_ge_bound; create_prop_decl Paxiom rec_pr t_delta_x; new_goal]
    | Dprop (p, pr, t) ->
        if !x_is_passed then
          begin
            delta_x := d :: !delta_x;
            [create_prop_decl p pr (replace_in_term x (t_app_infer plus_int [x; one_int]) t)]
          end
        else
          [d]
    | Dind _ | Dlogic _ | Dtype _ | Ddata _ ->
      if !x_is_passed then
        raise (Arg_trans "induction Dlogic")
      else
        [d]
    | Dparam _ls ->
      if !x_is_passed then
        begin
          delta_x := d :: !delta_x;
          [d]
        end
      else
        [d]
    (* TODO | Dlogic l ->
        if !x_is_passed then replace things inside and rebuild it else
        [d]*)
    ) None in
  Trans.par [le_bound; ge_bound]

let () = wrap_and_register
    ~desc:"induction <term1> [from] <term2> performs induction on int term1 from int term2. term2 is optional and default to 0."
    "induction"
    (Tterm (Topt ("from", Tterm Tenvtrans_l))) induction
