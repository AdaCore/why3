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
open Ident
open Ty
open Decl
open Args_wrapper
open Generic_arg_trans_utils

(** This file contains transformation with arguments that acts directly on a
    logic connector for intro (case, or_intro, intros, exists) *)

(** Explanations *)

(* Explanation for [left]/[right] *)
let left_case_expl = "left case"
let right_case_expl = "right case"

(* Explanation for [case] *)
let true_case_expl = "true case"
let false_case_expl = "false case"

(* Add an explanation attribute to a goal *)
let create_goal_trans ~expl =
  Trans.goal (fun pr g -> [create_goal ~expl pr g])

(* From task [delta |- G] and term t, build the tasks:
   [delta, t] |- G] and [delta, not t | - G] *)
let case t name =
  let name =
    match name with
    | Some name -> name
    | None -> "h"
  in
  let h = Decl.create_prsymbol (gen_ident name) in
  let hnot = Decl.create_prsymbol (gen_ident name) in
  let t_not_decl = Decl.create_prop_decl Decl.Paxiom hnot (Term.t_not t) in
  let t_decl = Decl.create_prop_decl Decl.Paxiom h t in
  let left_trans = Trans.compose (create_goal_trans ~expl:true_case_expl)
      (Trans.add_decls [t_decl]) in
  let right_trans = Trans.compose (create_goal_trans ~expl:false_case_expl)
      (Trans.add_decls [t_not_decl]) in
  Trans.par [left_trans; right_trans]

let or_intro (left: bool) : Task.task Trans.trans =
  Trans.decl (fun d ->
    match d.d_node with
    | Dprop (Pgoal, pr, t) ->
      begin
        match t.t_node with
        | Tbinop (Tor, t1, t2) ->
          if left then
            [create_goal ~expl:left_case_expl pr t1]
          else
            [create_goal ~expl:right_case_expl pr t2]
        | _ -> [d]
      end
    | _ -> [d]) None

let exists_aux g x =
  let t = subst_exist g x in
  let pr_goal = create_prsymbol (gen_ident "G") in
  let new_goal = Decl.create_prop_decl Decl.Pgoal pr_goal t in
  [new_goal]

(* From task [delta |- exists x. G] and term t, build
   the task  [delta |- G[x -> t]].
   Return an error if x and t are not unifiable. *)
let exists x =
  Trans.goal (fun _ g -> exists_aux g x)

(* TODO temporary *)
let rec intros list_name pr f =
  if list_name = [] then [create_prop_decl Pgoal pr f] else
  match f.t_node with
  | Tbinop (Timplies,f1,f2) ->
      (* f is going to be removed, preserve its attributes and location in f2 *)
      let f2 = t_attr_copy f f2 in
      let name, tl =
        match list_name with
        | [] -> assert false
        | "" :: tl -> "H", tl
        | name :: tl -> name, tl
      in
      let id = create_prsymbol (id_fresh name) in
      let d = create_prop_decl Paxiom id f1 in
      d :: intros tl pr f2
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let intro_var name subst vs =
        let ls = create_lsymbol name [] (Some vs.vs_ty) in
        Mvs.add vs (fs_app ls [] vs.vs_ty) subst,
        create_param_decl ls
      in

      (* TODO clarify this: We iterate on both the list of names given by the
         user and the list of variables bounded by the forall. The two lists can
         have different sizes and this solution is ugly. Should use a List
         function instead.  *)
      let rec subst_decls (subst, decls) list_name vsl =
        match list_name, vsl with
        | [], _ -> (subst, decls, vsl, [])
        | _, [] -> (subst, decls, [], list_name)
        | name :: list_name, var :: vsl ->
            let name = if name = "" then id_clone var.vs_name else id_fresh name in
            let subst, decl = intro_var name subst var in
            subst_decls (subst, decl :: decls) list_name vsl
      in

      let subst, decls, vsl, list_name = subst_decls (Mvs.empty, []) list_name vsl in
      if vsl = [] then
        let f = t_attr_copy f (t_subst subst f_t) in
        (List.rev decls) @ intros list_name pr f
      else
        let f = t_quant Tforall
            (t_close_quant vsl [] (t_subst subst f_t)) in
        (List.rev decls) @ intros list_name pr f

  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      let name =  List.hd list_name in
      let ls = create_lsymbol (id_fresh name) [] (Some vs.vs_ty) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros (List.tl list_name) pr f
  (* Intentionnaly do not fail when too many arguments are given *)
  | _ -> [create_prop_decl Pgoal pr f]

let intros list_name pr f =
  let tvs = t_ty_freevars Stv.empty f in
  let mk_ts tv () = create_tysymbol (id_clone tv.tv_name) [] NoDef in
  let tvm = Mtv.mapi mk_ts tvs in
  let decls = Mtv.map create_ty_decl tvm in
  let subst = Mtv.map (fun ts -> ty_app ts []) tvm in
  Mtv.values decls @ intros list_name pr (t_ty_subst subst Mvs.empty f)

(* TODO solve this inefficiency *)
let rec create_list n = if n <= 0 then [] else "" :: create_list (n-1)

(* TODO inefficient create_list *)
let introduce_premises n = Trans.goal (intros (create_list n))

let intros_list l = Trans.goal (intros l)

let () = wrap_and_register
    ~desc:"case <term> [name] generates hypothesis 'name: term' in a first goal and 'name: ~ term' in a second one."
    "case"
    (Tformula (Topt ("as",Tstring Ttrans_l))) case

let () = wrap_and_register ~desc:"left transform a disjunctive goal A \\/ B into A"
    "left"
    (Ttrans) (or_intro true)

let () = wrap_and_register ~desc:"right transform a disjunctive goal A \\/ B into B"
    "right"
    (Ttrans) (or_intro false)

let () = wrap_and_register
    ~desc:"exists <term> substitutes the existentially quantified variable with the given term"
    "exists"
    (Tterm Ttrans) exists

let () = wrap_and_register ~desc:"intros n introduces the first n quantified variables and hypotheses"
    "intros_n"
    (Tint Ttrans) introduce_premises

let () = wrap_and_register ~desc:"intros id1,id2,...,idk introduces quantified variables and hypotheses using the given identifiers names"
    "intros"
    (Tidentlist Ttrans) intros_list
