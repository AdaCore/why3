(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl

let apply_rev_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc l

let apply_append fn acc l = apply_rev_append fn acc (List.rev l)

let apply_append2 fn acc l1 l2 =
  Lists.fold_product (fun l e1 e2 -> fn e1 e2 :: l)
    acc (List.rev l1) (List.rev l2)

let split_case forig spl pos acc tl bl =
  let c = if pos then t_true else t_false in
  let bl = List.rev_map t_open_branch_cb bl in
  let bll,_ = List.fold_left (fun (bll,el) (pl,f,close) ->
    let spf = spl [] f in
    let brc = close pl c in
    let bll = List.map (fun rl -> brc::rl) bll in
    let bll = apply_append (fun f -> close pl f :: el) bll spf in
    bll, brc::el) ([],[]) bl
  in
  let fn bl = t_label_copy forig (t_case tl bl) in
  apply_append fn acc bll

let compiled = Ident.create_label "split_goal: compiled match"

let split_case_2 kn forig spl pos acc t bl =
  let vs = create_vsymbol (id_fresh "q") (t_type t) in
  let tv = t_var vs in
  let conn f = t_label_copy forig (t_let_close_simp vs t f) in
  let qn = if pos then t_forall_close_simp else t_exists_close_simp in
  let jn = if pos then t_implies_simp else t_and_simp in
  let _, bll = List.fold_left (fun (cseen,acc) b ->
    let p, f = t_open_branch b in
    match p.pat_node with
    | Pwild ->
        let csl,sbs = match p.pat_ty.ty_node with
          | Tyapp (ts,_) ->
              Decl.find_constructors kn ts,
              let ty = ty_app ts (List.map ty_var ts.ts_args) in
              ty_match Mtv.empty ty p.pat_ty
          | _ -> assert false in
        let csall = Sls.of_list (List.rev_map fst csl) in
        let csnew = Sls.diff csall cseen in
        assert (not (Sls.is_empty csnew));
        let add_cs cs g =
          let mk_v ty = create_vsymbol (id_fresh "w") (ty_inst sbs ty) in
          let vl = List.map mk_v cs.ls_args in
          let f = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
          t_or_simp g (t_exists_close_simp vl [] f) in
        let g = Sls.fold add_cs csnew t_false in
        let conn f = conn (jn g f) in
        csall, apply_rev_append conn acc (spl [] f)
    | Papp (cs, pl) ->
        let vl = List.map (function
          | {pat_node = Pvar v} -> v | _ -> assert false) pl in
        let g = t_equ tv (fs_app cs (List.map t_var vl) p.pat_ty) in
        let conn f = conn (qn vl [] (jn g f)) in
        assert (not (Sls.mem cs cseen));
        Sls.add cs cseen, apply_rev_append conn acc (spl [] f)
    | _ -> assert false) (Sls.empty,[]) bl
  in
  List.rev_append bll acc

let split_case_2 kn forig spl pos acc t bl =
  if Slab.mem compiled forig.t_label then
    let lab = Slab.remove compiled forig.t_label in
    let forig = t_label ?loc:forig.t_loc lab forig in
    split_case_2 kn forig spl pos acc t bl
  else
    let mk_let = t_let_close_simp in
    let mk_case t bl = t_label_add compiled (t_case_close t bl) in
    let mk_b b = let p,f = t_open_branch b in [p], f in
    let f = Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl) in
    spl acc f

let stop_split = Ident.create_label "stop_split"

let stop f = Slab.mem stop_split f.t_label
let asym f = Slab.mem Term.asym_label f.t_label
let keep f = Slab.mem Term.keep_on_simp_label f.t_label

let unstop f =
  t_label ?loc:f.t_loc (Slab.remove stop_split f.t_label) f

type split = {
  right_only : bool;
  stop_label : bool;
  respect_as : bool;
  comp_match : known_map option;
}

let rec split_pos ro acc f = match f.t_node with
  | _ when ro.stop_label && stop f -> unstop f :: acc
  | Ttrue -> if keep f then f::acc else acc
  | Tfalse -> f::acc
  | Tapp _ -> f::acc
  | Tbinop (Tand,f1,f2) when ro.respect_as && asym f1 ->
      split_pos ro (split_pos ro acc (t_implies f1 f2)) f1
  | Tbinop (Tand,f1,f2) ->
      split_pos ro (split_pos ro acc f2) f1
  | Tbinop (Timplies,f1,f2) when ro.right_only ->
      let fn f2 = t_label_copy f (t_implies f1 f2) in
      apply_append fn acc (split_pos ro [] f2)
  | Tbinop (Timplies,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_implies f1 f2) in
      apply_append2 fn acc (split_neg ro [] f1) (split_pos ro [] f2)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_label_copy f (t_implies f1 f2) in
      let f21 = t_label_copy f (t_implies f2 f1) in
      split_pos ro (split_pos ro acc f21) f12
  | Tbinop (Tor,_,_) when ro.right_only -> f::acc
  | Tbinop (Tor,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_or f1 f2) in
      apply_append2 fn acc (split_pos ro [] f1) (split_pos ro [] f2)
  | Tnot f1 ->
      let fn f1 = t_label_copy f (t_not f1) in
      apply_append fn acc (split_neg ro [] f1)
  | Tif (fif,fthen,felse) ->
      let fit = t_label_copy f (t_implies fif fthen) in
      let fie = t_label_copy f (t_implies (t_not fif) felse) in
      split_pos ro (split_pos ro acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split_pos ro [] f1)
  | Tcase (tl,bl) when ro.comp_match <> None ->
      split_case_2 (Opt.get ro.comp_match) f (split_pos ro) true acc tl bl
  | Tcase (tl,bl) ->
      split_case f (split_pos ro) true acc tl bl
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_forall (close vsl trl f1)) in
      apply_append fn acc (split_pos ro [] f1)
  | Tquant (Texists,_) -> f::acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and split_neg ro acc f = match f.t_node with
  | _ when ro.stop_label && stop f -> unstop f :: acc
  | Ttrue -> f::acc
  | Tfalse -> if keep f then f::acc else acc
  | Tapp _ -> f::acc
  | Tbinop (Tand,_,_) when ro.right_only -> f::acc
  | Tbinop (Tand,f1,f2) ->
      let fn f1 f2 = t_label_copy f (t_and f1 f2) in
      apply_append2 fn acc (split_neg ro [] f1) (split_neg ro [] f2)
  | Tbinop (Timplies,f1,f2) when ro.respect_as && asym f1 ->
      split_neg ro (split_neg ro acc (t_and f1 f2)) (t_not f1)
  | Tbinop (Timplies,f1,f2) ->
      split_neg ro (split_neg ro acc f2) (t_not f1)
  | Tbinop (Tiff,f1,f2) ->
      let f12 = t_label_copy f (t_and f1 f2) in
      let f21 = t_label_copy f (t_and (t_not f1) (t_not f2)) in
      split_neg ro (split_neg ro acc f21) f12
  | Tbinop (Tor,f1,f2) when ro.respect_as && asym f1 ->
      split_neg ro (split_neg ro acc (t_and (t_not f1) f2)) f1
  | Tbinop (Tor,f1,f2) ->
      split_neg ro (split_neg ro acc f2) f1
  | Tnot f1 ->
      let fn f1 = t_label_copy f (t_not f1) in
      apply_append fn acc (split_pos ro [] f1)
  | Tif (fif,fthen,felse) ->
      let fit = t_label_copy f (t_and fif fthen) in
      let fie = t_label_copy f (t_and (t_not fif) felse) in
      split_neg ro (split_neg ro acc fie) fit
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      apply_append fn acc (split_neg ro [] f1)
  | Tcase (tl,bl) when ro.comp_match <> None ->
      split_case_2 (Opt.get ro.comp_match) f (split_neg ro) false acc tl bl
  | Tcase (tl,bl) ->
      split_case f (split_neg ro) false acc tl bl
  | Tquant (Texists,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_exists (close vsl trl f1)) in
      apply_append fn acc (split_neg ro [] f1)
  | Tquant (Tforall,_) -> f::acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

let full_split kn = {
  right_only = false;
  stop_label = false;
  respect_as = true;
  comp_match = kn;
}

let right_split kn = { (full_split kn) with right_only = true }
let wp_split kn    = { (right_split kn) with stop_label = true }
let intro_split kn = { (wp_split kn) with respect_as = false }

let split_pos_full ?known_map f = split_pos (full_split known_map) [] f
let split_neg_full ?known_map f = split_neg (full_split known_map) [] f

let split_pos_right ?known_map f = split_pos (right_split known_map) [] f
let split_neg_right ?known_map f = split_neg (right_split known_map) [] f

let split_pos_wp ?known_map f = split_pos (wp_split known_map) [] f
let split_neg_wp ?known_map f = split_neg (wp_split known_map) [] f

let split_pos_intro ?known_map f = split_pos (intro_split known_map) [] f
let split_neg_intro ?known_map f = split_neg (intro_split known_map) [] f

let split_goal ro pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split_pos ro [] f)

let split_axiom ro pr f =
  let make_prop f =
    let pr = create_prsymbol (id_clone pr.pr_name) in
    create_prop_decl Paxiom pr f in
  let ro = { ro with respect_as = false } in
  match split_pos ro [] f with
    | [f] -> [create_prop_decl Paxiom pr f]
    | fl  -> List.map make_prop fl

let split_all ro d = match d.d_node with
  | Dprop (Pgoal, pr,f) ->  split_goal  ro pr f
  | Dprop (Paxiom,pr,f) -> [split_axiom ro pr f]
  | _ -> [[d]]

let split_premise ro d = match d.d_node with
  | Dprop (Paxiom,pr,f) ->  split_axiom ro pr f
  | _ -> [d]

let prep_goal split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.goal_l (split_goal split) in
  Trans.apply trans t)

let prep_all split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.decl_l (split_all split) None in
  Trans.apply trans t)

let prep_premise split = Trans.store (fun t ->
  let split = split (Some (Task.task_known t)) in
  let trans = Trans.decl (split_premise split) None in
  Trans.apply trans t)

let split_goal_full  = prep_goal full_split
let split_goal_right = prep_goal right_split
let split_goal_wp    = prep_goal wp_split

let split_all_full  = prep_all full_split
let split_all_right = prep_all right_split
let split_all_wp    = prep_all wp_split

let split_premise_full  = prep_premise full_split
let split_premise_right = prep_premise right_split
let split_premise_wp    = prep_premise wp_split

let () = Trans.register_transform_l "split_goal_full" split_goal_full
  ~desc:"Put@ the@ goal@ in@ a@ conjunctive@ form,@ \
  returns@ the@ corresponding@ set@ of@ subgoals.@ The@ number@ of@ subgoals@ \
  generated@ may@ be@ exponential@ in@ the@ size@ of@ the@ initial@ goal."
let () = Trans.register_transform_l "split_all_full" split_all_full
  ~desc:"Same@ as@ split_goal_full,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_full" split_premise_full
  ~desc:"Same@ as@ split_all_full,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_right" split_goal_right
  ~desc:"@[<hov 2>Same@ as@ split_goal_full,@ but@ don't@ split:@,\
      - @[conjunctions under disjunctions@]@\n\
      - @[conjunctions on the left of implications.@]@]"
let () = Trans.register_transform_l "split_all_right" split_all_right
  ~desc:"Same@ as@ split_goal_right,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_right" split_premise_right
  ~desc:"Same@ as@ split_all_right,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_wp" split_goal_wp
  ~desc:"Same@ as@ split_goal_right,@ but@ stops@ at@ \
    the@ `stop_split'@ label@ and@ removes@ the@ label."
let () = Trans.register_transform_l "split_all_wp" split_all_wp
  ~desc:"Same@ as@ split_goal_wp,@ but@ also@ split@ premises."
let () = Trans.register_transform "split_premise_wp" split_premise_wp
  ~desc:"Same@ as@ split_all_wp,@ but@ split@ only@ premises."

let () = Trans.register_transform_l "split_goal_wp_old"
  (Trans.goal_l (split_goal (wp_split None)))
  ~desc:"transitional, to be removed as soon as all sessions migrate"

let ls_of_var v =
  create_fsymbol (id_fresh ("spl_" ^ v.vs_name.id_string)) [] v.vs_ty

let split_intro known_map pr f =
  let rec split_intro dl acc f =
    let rsp = split_intro dl in
    match f.t_node with
    | Ttrue when not (keep f) -> acc
    | Tbinop (Tand,f1,f2) when asym f1 ->
        rsp (rsp acc (t_implies f1 f2)) f1
    | Tbinop (Tand,f1,f2) ->
        rsp (rsp acc f2) f1
    | Tbinop (Timplies,f1,f2) ->
        let pp = create_prsymbol (id_fresh (pr.pr_name.id_string ^ "_spl")) in
        let dl = create_prop_decl Paxiom pp f1 :: dl in
        split_intro dl acc f2
    | Tbinop (Tiff,f1,f2) ->
        rsp (rsp acc (t_implies f2 f1)) (t_implies f1 f2)
    | Tif (fif,fthen,felse) ->
        rsp (rsp acc (t_implies (t_not fif) felse)) (t_implies fif fthen)
    | Tlet (t,fb) -> let vs,f = t_open_bound fb in
        let ls = ls_of_var vs in
        let f  = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
        let dl = create_logic_decl [make_ls_defn ls [] t] :: dl in
        split_intro dl acc f
    | Tquant (Tforall,fq) -> let vsl,_,f = t_open_quant fq in
        let lls = List.map ls_of_var vsl in
        let add s vs ls = Mvs.add vs (fs_app ls [] vs.vs_ty) s in
        let f = t_subst (List.fold_left2 add Mvs.empty vsl lls) f in
        let add dl ls = create_param_decl ls :: dl in
        let dl = List.fold_left add dl lls in
        split_intro dl acc f
    | _ ->
        let goal f = List.rev (create_prop_decl Pgoal pr f :: dl) in
        List.rev_append (List.rev_map goal (split_pos_wp ~known_map f)) acc
  in
  split_intro [] [] f

let split_intro = Trans.store (fun t ->
  Trans.apply (Trans.goal_l (split_intro (Task.task_known t))) t)

let () = Trans.register_transform_l "split_intro" split_intro
  ~desc:"Same@ as@ split_goal_wp,@ but@ moves@ \
    the@ implication@ antecedents@ to@ premises."
