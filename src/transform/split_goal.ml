(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident
open Term
open Decl

let apply_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc (List.rev l)

let apply_append2 fn acc l1 l2 =
  Util.list_fold_product (fun l e1 e2 -> fn e1 e2 :: l)
    acc (List.rev l1) (List.rev l2)

let split_case spl c acc tl bl =
  let bl = List.rev_map f_open_branch bl in
  let bll,_ = List.fold_left (fun (bll,el) (pl,f) ->
    let spf = spl [] f in
    let brc = f_close_branch pl c in
    let bll = List.map (fun rl -> brc::rl) bll in
    let bll = apply_append (fun f -> f_close_branch pl f :: el) bll spf in
    bll, brc::el) ([],[]) bl
  in
  apply_append (f_case tl) acc bll

let asym_split = Ident.label "asym_split"

let to_split f = List.exists (fun (l,_) -> l = "asym_split") f.f_label

let rec split_pos ro acc f = match f.f_node with
  | Ftrue -> acc
  | Ffalse -> f::acc
  | Fapp _ -> f::acc
  | Fbinop (Fand,f1,f2) when to_split f ->
      split_pos ro (split_pos ro acc (f_implies f1 f2)) f1
  | Fbinop (Fand,f1,f2) ->
      split_pos ro (split_pos ro acc f2) f1
  | Fbinop (Fimplies,f1,f2) when ro ->
      apply_append (f_implies f1) acc (split_pos ro [] f2)
  | Fbinop (Fimplies,f1,f2) ->
      apply_append2 f_implies acc (split_neg ro [] f1) (split_pos ro [] f2)
  | Fbinop (Fiff,f1,f2) ->
      split_pos ro (split_pos ro acc (f_implies f2 f1)) (f_implies f1 f2)
  | Fbinop (For,f1,f2) when ro ->
      apply_append (f_or f1) acc (split_pos ro [] f2)
  | Fbinop (For,f1,f2) ->
      apply_append2 f_or acc (split_pos ro [] f1) (split_pos ro [] f2)
  | Fnot f ->
      apply_append f_not acc (split_neg ro [] f)
  | Fif (fif,fthen,felse) ->
      let acc = split_pos ro acc (f_implies (f_not fif) felse) in
      split_pos ro acc (f_implies fif fthen)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      apply_append (f_let_close vs t) acc (split_pos ro [] f)
  | Fcase (tl,bl) ->
      split_case (split_pos ro) f_true acc tl bl
  | Fquant (Fforall,fq) -> let vsl,trl,f = f_open_quant fq in
      (* TODO : Remove unused variable *)
      apply_append (f_forall_close vsl trl) acc (split_pos ro [] f)
  | Fquant (Fexists,_) -> f::acc

and split_neg ro acc f = match f.f_node with
  | Ftrue -> f::acc
  | Ffalse -> acc
  | Fapp _ -> f::acc
  | Fbinop (Fand,f1,f2) when ro ->
      apply_append (f_and f1) acc (split_neg ro [] f2)
  | Fbinop (Fand,f1,f2) ->
      apply_append2 f_and acc (split_neg ro [] f1) (split_neg ro [] f2)
  | Fbinop (Fimplies,f1,f2) when to_split f ->
      split_neg ro (split_neg ro acc (f_and f1 f2)) (f_not f1)
  | Fbinop (Fimplies,f1,f2) ->
      split_neg ro (split_neg ro acc f2) (f_not f1)
  | Fbinop (Fiff,f1,f2) ->
      let acc = split_neg ro acc (f_and (f_not f1) (f_not f2)) in
      split_neg ro acc (f_and f1 f2)
  | Fbinop (For,f1,f2) when to_split f ->
      split_neg ro (split_neg ro acc (f_and (f_not f1) f2)) f1
  | Fbinop (For,f1,f2) ->
      split_neg ro (split_neg ro acc f2) f1
  | Fnot f ->
      apply_append f_not acc (split_pos ro [] f)
  | Fif (fif,fthen,felse) ->
      let acc = split_neg ro acc (f_and (f_not fif) felse) in
      split_neg ro acc (f_and fif fthen)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      apply_append (f_let_close vs t) acc (split_neg ro [] f)
  | Fcase (tl,bl) ->
      split_case (split_neg ro) f_false acc tl bl
  | Fquant (Fexists,fq) -> let vsl,trl,f = f_open_quant fq in
      (* TODO : Remove unused variable *)
      apply_append (f_exists_close vsl trl) acc (split_neg ro [] f)
  | Fquant (Fforall,_) -> f::acc

let split_goal ro pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split_pos ro [] f)

let split_axiom ro pr f =
  let make_prop f =
    let pr = create_prsymbol (id_clone pr.pr_name) in
    create_prop_decl Paxiom pr f
  in
  List.map make_prop (split_pos ro [] f)

let split_all ro d = match d.d_node with
  | Dprop (Pgoal, pr,f) ->  split_goal  ro pr f
  | Dprop (Paxiom,pr,f) -> [split_axiom ro pr f]
  | _ -> [[d]]

let split_premise ro d = match d.d_node with
  | Dprop (Paxiom,pr,f) ->  split_axiom ro pr f
  | _ -> [d]

let full_split_pos = split_pos false []
let full_split_neg = split_neg false []

let split_pos = split_pos true []
let split_neg = split_neg true []

let full_split_goal    = Trans.goal_l (split_goal    false)
let full_split_all     = Trans.decl_l (split_all     false) None
let full_split_premise = Trans.decl   (split_premise false) None

let split_goal    = Trans.goal_l (split_goal    true)
let split_all     = Trans.decl_l (split_all     true) None
let split_premise = Trans.decl   (split_premise true) None

let () = Trans.register_transform_l "split_goal"    split_goal
let () = Trans.register_transform_l "split_all"     split_all
let () = Trans.register_transform   "split_premise" split_premise

let () = Trans.register_transform_l "full_split_goal"    full_split_goal
let () = Trans.register_transform_l "full_split_all"     full_split_all
let () = Trans.register_transform   "full_split_premise" full_split_premise

let ls_of_var v =
  create_fsymbol (id_fresh ("spl_" ^ v.vs_name.id_string)) [] v.vs_ty

let rec split_intro pr dl acc f =
  let rsp = split_intro pr dl in
  match f.f_node with
  | Ftrue -> acc
  | Fbinop (Fand,f1,f2) when to_split f ->
      rsp (rsp acc (f_implies f1 f2)) f1
  | Fbinop (Fand,f1,f2) ->
      rsp (rsp acc f2) f1
  | Fbinop (Fimplies,f1,f2) ->
      let pp = create_prsymbol (id_fresh (pr.pr_name.id_string ^ "_spl")) in
      let dl = create_prop_decl Paxiom pp f1 :: dl in
      split_intro pr dl acc f2
  | Fbinop (Fiff,f1,f2) ->
      rsp (rsp acc (f_implies f2 f1)) (f_implies f1 f2)
  | Fif (fif,fthen,felse) ->
      rsp (rsp acc (f_implies (f_not fif) felse)) (f_implies fif fthen)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      let ls = ls_of_var vs in
      let f  = f_subst_single vs (t_app ls [] vs.vs_ty) f in
      let dl = create_logic_decl [make_fs_defn ls [] t] :: dl in
      split_intro pr dl acc f
  | Fquant (Fforall,fq) -> let vsl,_,f = f_open_quant fq in
      let lls = List.map ls_of_var vsl in
      let add s vs ls = Mvs.add vs (t_app ls [] vs.vs_ty) s in
      let f = f_subst (List.fold_left2 add Mvs.empty vsl lls) f in
      let add dl ls = create_logic_decl [ls, None] :: dl in
      let dl = List.fold_left add dl lls in
      split_intro pr dl acc f
  | _ ->
      let goal f = List.rev (create_prop_decl Pgoal pr f :: dl) in
      List.rev_append (List.rev_map goal (split_pos f)) acc

let split_intro = Trans.goal_l (fun pr f -> split_intro pr [] [] f)

let () = Trans.register_transform_l "split_intro" split_intro

