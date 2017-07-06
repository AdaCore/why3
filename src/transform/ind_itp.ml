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

let induction x bound env =
  let th = Env.read_theory env ["int"] "Int" in
  let le_int = Theory.ns_find_ls th.Theory.th_export ["infix <="] in
  let plus_int = Theory.ns_find_ls th.Theory.th_export ["infix +"] in
  let one_int =
    Term.t_const (Number.ConstInt (Number.int_const_dec "1")) Ty.ty_int in

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
        let pr = create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "H")) nt in
        [pr; d]
    | _ -> [d]) None in

  let x_is_passed = ref false in
  let ge_bound =
    Trans.decl (fun d -> match d.d_node with
    | Dparam (ls) when (Ident.id_equal lsx ls.ls_name) ->
        (x_is_passed := true; [d])
    | Dprop (Pgoal, pr, t) ->
        if not (!x_is_passed) then
          raise (Arg_trans "induction")
        else
          let x_ge_bound_t = t_app_infer le_int [bound; x] in
          let x_ge_bound =
            create_prop_decl Paxiom (Decl.create_prsymbol (gen_ident "H")) x_ge_bound_t in
          let new_pr = create_prsymbol (gen_ident "G") in
          let new_goal = create_prop_decl Pgoal new_pr
              (replace_in_term x (t_app_infer plus_int [x; one_int]) t) in
          [x_ge_bound; create_prop_decl Paxiom pr t; new_goal]
    | Dprop (p, pr, t) ->
        if !x_is_passed then [create_prop_decl p pr (replace_in_term x (t_app_infer plus_int [x; one_int]) t)] else [d]
    (* TODO | Dlogic l ->
        if !x_is_passed then replace things inside and rebuild it else
        [d]*)
    | _ -> [d]) None in
  Trans.par [le_bound; ge_bound]

let () = wrap_and_register
    ~desc:"induction <term1> <term2> performs induction on int term1 from int term2"
    "induction"
    (Tterm (Tterm Tenvtrans_l)) induction
