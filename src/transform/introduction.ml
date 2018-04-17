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

(*
  This module was poorly designed by Claude Marché, with the
  enormous help of Jean-Christophe Filliâtre and Andrei Paskevich
  for finding the right function in the Why3 API
*)

open Ident
open Ty
open Term
open Decl

let stop f = Slab.mem Term.stop_split f.t_label

let case_split = Ident.create_label "case_split"
let case f = Slab.mem case_split f.t_label

let rec dequant pos f = t_label_copy f (match f.t_node with
  | _ when stop f -> f
  | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) })
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,_,{ t_node = Ttrue }) },f1) ->
      dequant pos f1
  | Tbinop (Tand,f1,f2) when not pos ->
      t_and (dequant false f1) (dequant false f2)
  | Tbinop (Tand,f1,f2) ->
      t_and (dequant_if_case true f1) (dequant_if_case true f2)
  | Tbinop (Tor,f1,f2) when pos ->
      t_or (dequant true f1) (dequant true f2)
  | Tbinop (Tor,f1,f2) ->
      t_or (dequant_if_case false f1) (dequant_if_case false f2)
  | Tbinop (Timplies,f1,f2) when pos ->
      t_implies (dequant false f1) (dequant true f2)
  | Tbinop (Timplies,f1,f2) ->
      t_implies (dequant_if_case true f1) (dequant_if_case false f2)
  | Tbinop (Tiff,_,_) -> f
  | Tif (fif,fthen,felse) ->
      t_if fif (dequant pos fthen) (dequant pos felse)
  | Tnot f1 ->
      t_not (dequant (not pos) f1)
  | Tlet (t,fb) ->
      let vs, f1 = t_open_bound fb in
      t_let_close vs t (dequant pos f1)
  | Tcase (t,bl) ->
      let branch bf =
        let pat, f1 = t_open_branch bf in
        t_close_branch pat (dequant pos f1) in
      t_case t (List.map branch bl)
  | Tquant (Tforall,fq) when pos ->
      let _,_,f1 = t_open_quant fq in
      dequant true f1
  | Tquant (Texists,fq) when not pos ->
      let _,_,f1 = t_open_quant fq in
      dequant false f1
  | Tquant _ | Ttrue | Tfalse | Tapp _ -> f
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f))

and dequant_if_case pos f = if case f then dequant pos f else f

let intro_var subst ({vs_name = id; vs_ty = ty} as vs) =
  let ls = create_fsymbol (id_clone id) [] ty in
  Mvs.add vs (fs_app ls [] ty) subst,
  create_param_decl ls

let rec intros kn pr f =
  match f.t_node with
  (* (f2 \/ True) => _ *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },_)
      when Slab.mem Term.asym_split f2.t_label ->
        [create_prop_decl Pgoal pr f]
  | Tbinop (Timplies,f1,f2) ->
      (* split f1 *)
      (* f is going to be removed, preserve its labels and location in f2  *)
      let f2 = t_label_copy f f2 in
      let fl = Split_goal.split_intro_right ?known_map:kn (dequant false f1) in
      let add (subst,dl) f =
        let svs = Mvs.set_diff (t_freevars Mvs.empty f) subst in
        let subst, dl = Mvs.fold (fun vs _ (subst,dl) ->
          let subst, d = intro_var subst vs in
          subst, d::dl) svs (subst, dl) in
        let prx = create_prsymbol (id_fresh "H") in
        let d = create_prop_decl Paxiom prx (t_subst subst f) in
        subst, d::dl in
      let _, fl = List.fold_left add (Mvs.empty, []) fl in
      List.rev_append fl (intros kn pr f2)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let subst, dl = Lists.map_fold_left intro_var Mvs.empty vsl in
      (* preserve labels and location of f  *)
      let f = t_label_copy f (t_subst subst f_t) in
      dl @ intros kn pr f
  | Tlet (t,fb) ->
      let vs,f = t_open_bound fb in
      let ls = create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros kn pr f
  | _ -> [create_prop_decl Pgoal pr f]

let intros ?known_map pr f =
  let tvs = t_ty_freevars Stv.empty f in
  let mk_ts tv () = create_tysymbol (id_clone tv.tv_name) [] NoDef in
  let tvm = Mtv.mapi mk_ts tvs in
  let decls = Mtv.map create_ty_decl tvm in
  let subst = Mtv.map (fun ts -> ty_app ts []) tvm in
  Mtv.values decls @ intros known_map pr (t_ty_subst subst Mvs.empty f)

(*
FIXME [merge from itp]: What was the role of this known_map ??

let introduce_premises = Trans.store (fun t ->
  let known_map = Task.task_known t in
  Trans.apply (Trans.goal (intros ~known_map)) t)

 *)

let intros_with_meta pr f =
  let l = intros pr f in
  Theory.create_meta Pretty.meta_introduced_hypotheses [] ::
  List.rev (List.rev_map Theory.create_decl l)

let introduce_premises = Trans.tgoal intros_with_meta


let () = Trans.register_transform "introduce_premises" introduce_premises
  ~desc:"Introduce@ universal@ quantification@ and@ hypothesis@ in@ the@ \
         goal@ into@ constant@ symbol@ and@ axioms."


(** Destruction of existential quantifiers in axioms.
    Contributed by Nicolas Jeannerod [niols@niols.fr] *)
let rec eliminate_exists_aux pr t =
  match t.t_node with
  | Tquant (Texists, q) ->
     let vsl, _, t' = t_open_quant q in
     let intro_var subst vs =
       let ls =
         create_lsymbol (id_clone vs.vs_name) [] (Some vs.vs_ty)
       in
       Mvs.add vs (fs_app ls [] vs.vs_ty) subst, create_param_decl ls
     in
     let subst, dl = Lists.map_fold_left intro_var Mvs.empty vsl in
     let t' = t_subst subst t' in
     let t = t_label_copy t t' in
     dl @ eliminate_exists_aux pr t
  | _ ->
     [create_prop_decl Paxiom pr t]

let eliminate_exists d =
  match d.d_node with
  | Dprop (Paxiom, pr, t) -> eliminate_exists_aux pr t
  | _ -> [d]

let () = Trans.register_transform
           "introduce_exists"
           (Trans.decl eliminate_exists None)
           ~desc:"Replace axioms of the form 'exists x. P' by 'constant x axiom P'."

let simplify_intros =
  Trans.compose Simplify_formula.simplify_trivial_wp_quantification
                introduce_premises

let split_intros_goal_wp =
  Trans.compose_l Split_goal.split_goal_right (Trans.singleton simplify_intros)

let split_intros_all_wp =
  Trans.compose_l Split_goal.split_all_right (Trans.singleton simplify_intros)

let split_intros_premise_wp =
  Trans.compose Split_goal.split_premise_right simplify_intros

let () = Trans.register_transform_l
           "split_intros_goal_wp" split_intros_goal_wp
           ~desc:"The@ recommended@ splitting@ transformation@ to@ apply@ \
              on@ VCs@ generated@ by@ WP@ (split_goal_right@ followed@ \
              by@ simplify_trivial_quantifications@ followed@ by@ \
              introduce_premises)."

let () = Trans.register_transform_l
           "split_intros_all_wp" split_intros_all_wp
           ~desc:"Same@ as@ split_intros_goal_wp,@ but@ also@ split@ premises."

let () = Trans.register_transform
           "split_intros_premise_wp" split_intros_premise_wp
           ~desc:"Same@ as@ split_intros_all_wp,@ but@ split@ only@ premises."
