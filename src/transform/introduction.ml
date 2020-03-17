(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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

let stop f = Sattr.mem Term.stop_split f.t_attrs

let case_split = Ident.create_attribute "case_split"
let case f = Sattr.mem case_split f.t_attrs

let meta_intro_ls = Theory.register_meta
  ~desc:"(internal@ use)@ Preserve@ an@ introduced@ logical@ symbol@ name@ \
        after@ generalization."
  "introduced_lsymbol" [Theory.MTlsymbol]

let meta_intro_pr = Theory.register_meta
  ~desc:"(internal@ use)@ Preserve@ an@ introduced@ proposition@ name@ \
        after@ generalization."
  "introduced_prsymbol" [Theory.MTprsymbol]

module Hsdecl = Hashcons.Make (struct
  type t = decl

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dprop (k1,pr1,f1), Dprop (k2,pr2,f2) ->
        let pr_equal {pr_name = id1} {pr_name = id2} =
          id1.id_string = id2.id_string &&
          Sattr.equal id1.id_attrs id2.id_attrs &&
          Opt.equal Loc.equal id1.id_loc id2.id_loc in
        k1 = k2 && pr_equal pr1 pr2 && t_equal_strict f1 f2
    | _,_ -> d_equal d1 d2

  let hash d = match d.d_node with
    | Dprop (k,pr,f) -> Hashcons.combine (Hashcons.combine
        (Hashtbl.hash pr.pr_name.id_string) (t_hash_strict f))
        (match k with Plemma -> 11 | Paxiom -> 13 | Pgoal -> 17)
    | _ -> d_hash d

  let tag _ d = d
end)

let apply_prev fn hd = match hd.Task.task_prev with
  | Some hd -> fn hd
  | None -> [], None

let apply_head fn = function
  | Some hd -> snd (fn hd)
  | None -> None

let rec dequant ht pos f =
  let dequant = dequant ht (* save the "open-to-bound" map in ht *) in
  let dequant_if_case pos f = if case f then dequant pos f else f in
  t_attr_copy f (match f.t_node with
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
      let vl,_,f1 = t_open_quant fq in
      List.iter2 (Hvs.replace ht) vl (t_peek_quant fq);
      dequant true f1
  | Tquant (Texists,fq) when not pos ->
      let vl,_,f1 = t_open_quant fq in
      List.iter2 (Hvs.replace ht) vl (t_peek_quant fq);
      dequant false f1
  | Tquant _ | Ttrue | Tfalse | Tapp _ -> f
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f))

let intro_attrs = Sattr.singleton Inlining.intro_attr

let compat ls vs =
  ls.ls_args = [] &&
  Opt.equal ty_equal ls.ls_value (Some vs.vs_ty) &&
  Opt.equal Loc.equal ls.ls_name.id_loc vs.vs_name.id_loc &&
  Sattr.equal ls.ls_name.id_attrs
    (Sattr.add Inlining.intro_attr vs.vs_name.id_attrs)

(* Memoize the correspondence between bound variables
   and introduced lsymbols to increase sharing *)

let ls_of_vs = let wt = Wid.create 7 in fun vs id ols ->
  try Wid.find wt id with Not_found ->
  let ls = match ols with Some ls -> ls | None ->
    let id = id_clone ~attrs:intro_attrs vs.vs_name in
    create_fsymbol id [] vs.vs_ty in
  Wid.set wt id ls; ls

let ls_of_vs mal vs id = match mal with
  | Theory.MAls ls :: mal when compat ls vs ->
         ls_of_vs vs id (Some ls), mal
  | _ -> ls_of_vs vs id None, mal

let intro_var (subst, mal) (vs, id) =
  let ls, mal = ls_of_vs mal vs id in
  let subst = Mvs.add vs (fs_app ls [] vs.vs_ty) subst in
  (subst, mal), create_param_decl ls

let get_expls f =
  Sattr.filter (fun a -> Strings.has_prefix "expl:" a.attr_string) f.t_attrs

let get_hyp_names f =
  Sattr.filter (fun a -> Strings.has_prefix "hyp_name:" a.attr_string) f.t_attrs

(* Check if we already have a proposition with the same content.
   If we have a hash-consed one, and it is not yet used in the task,
   then use it. If it is already in the task, then check if we have
   a similar proposition saved in a weak hash-table, that is not yet
   used in the task. If none is found, use the newly created decl. *)
let find_fresh_axiom = let wt = Wdecl.create 7 in fun axs d ->
  let o = Hsdecl.hashcons d in if not (Sdecl.mem o axs) then o else
  let spares = try Wdecl.find wt o with Not_found -> Sdecl.empty in
  try Sdecl.min_elt (Sdecl.diff spares axs) with Not_found ->
  Wdecl.set wt o (Sdecl.add d spares); d

let pr_of_premise f =
  let nm = Ident.get_hyp_name ~attrs:f.t_attrs in
  let nm = Opt.get_def "H" nm in
  create_prsymbol (id_fresh nm ~attrs:intro_attrs)

let rec intros kn pr axs mal (expl, hyp_name) f =
  let aux_move attrs fattrs = (* attrs may be [expl] or [hyp_name] *)
    let attrs = if Sattr.is_empty fattrs then attrs else fattrs in
    let move f =
      if Sattr.is_empty fattrs && not (Sattr.is_empty attrs)
      then t_attr_add (Sattr.min_elt attrs) f else f in
    attrs, move in
  let expl, move_expl = aux_move expl (get_expls f) in
  let hyp_name, move_hyp_name = aux_move hyp_name (get_hyp_names f) in
  let move_attrs f = move_expl (move_hyp_name f) in
  match f.t_node with
  (* (f2 \/ True) => _ *)
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },_)
      when Sattr.mem Term.asym_split f2.t_attrs ->
        [create_prop_decl Pgoal pr (move_attrs f)]
  | Tbinop (Timplies,f1,f2) ->
      (* f is going to be removed, preserve its attributes and location in f2 *)
      let f2 = t_attr_copy f f2 in
      (* dequantify and split f1, retaining the "open-to-bound" map *)
      let ht = Hvs.create 7 in
      let f1 = dequant ht false f1 in
      let fl = Split_goal.split_intro_right ?known_map:kn f1 in
      (* construct new premises, reusing lsymbols and propositions *)
      let add (subst,axs,dl) f =
        let svs = Mvs.set_diff (t_freevars Mvs.empty f) subst in
        let subst, dl = Mvs.fold (fun vs _ (subst,dl) ->
          let (subst,_), d = intro_var (subst, []) (vs, Hvs.find ht vs) in
          subst, d::dl) svs (subst, dl) in
        (* only reuse the name when fl is a singleton *)
        let prx = match mal, fl with
          | Theory.MApr pr :: _, [_] -> pr
          | _, _ -> pr_of_premise f in
        let d = create_prop_decl Paxiom prx (t_subst subst f) in
        let d = find_fresh_axiom axs d in
        subst, Sdecl.add d axs, d::dl in
      (* consume the topmost name *)
      let mal = match mal with
        | Theory.MApr _ :: mal -> mal
        | _ -> mal in
      let _,axs,dl = List.fold_left add (Mvs.empty,axs,[]) fl in
      List.rev_append dl (intros kn pr axs mal (expl, hyp_name) f2)
  | Tquant (Tforall,fq) ->
      let vsl,_trl,f_t = t_open_quant fq in
      let vsl = List.combine vsl (t_peek_quant fq) in
      let (subst, mal), dl =
        Lists.map_fold_left intro_var (Mvs.empty, mal) vsl in
      (* preserve attributes and location of f  *)
      let f = t_attr_copy f (t_subst subst f_t) in
      dl @ intros kn pr axs mal (expl, hyp_name) f
  | Tlet (t,fb) ->
      let vs, f = t_open_bound fb in
      let ls, mal = ls_of_vs mal vs (t_peek_bound fb) in
      let f = t_subst_single vs (fs_app ls [] vs.vs_ty) f in
      let d = create_logic_decl [make_ls_defn ls [] t] in
      d :: intros kn pr axs mal (expl, hyp_name) f
  | _ -> [create_prop_decl Pgoal pr (move_attrs f)]

let intros kn mal pr f =
  let tvs = t_ty_freevars Stv.empty f in
  let mk_ts tv () = create_tysymbol (id_clone tv.tv_name) [] NoDef in
  let tvm = Mtv.mapi mk_ts tvs in
  let decls = Mtv.map create_ty_decl tvm in
  let subst = Mtv.map (fun ts -> ty_app ts []) tvm in
  let f = t_ty_subst subst Mvs.empty f in
  let dl = intros kn pr Sdecl.empty mal (Sattr.empty, Sattr.empty) f in
  Mtv.values decls @ dl

let rec introduce hd =
  match hd.Task.task_decl.Theory.td_node with
  | Theory.Decl {d_node = Dprop (Pgoal,pr,f)} ->
      let mal, task = apply_prev introduce hd in
      let kn = Some (Task.task_known task) in
      let dl = intros kn (List.rev mal) pr f in
      [], List.fold_left Task.add_decl task dl
  | Theory.Meta (m,[ma])
    when Theory.meta_equal m meta_intro_ls ||
         Theory.meta_equal m meta_intro_pr ->
      let mal, task = apply_prev introduce hd in
      ma::mal, task
  | Theory.Meta _ ->
      let mal, task = apply_prev introduce hd in
      mal, Task.add_tdecl task hd.Task.task_decl
  | _ ->
      [], Some hd

let intros ?known_map pr f = intros known_map [] pr f

let introduce_premises = Trans.store (apply_head introduce)

let () = Trans.register_transform "introduce_premises" introduce_premises
  ~desc:"Introduce@ universal@ quantification@ and@ hypothesis@ in@ the@ \
         goal@ into@ constant@ symbol@ and@ axioms."

(* In this file t_replace is used to substitute vsymbol with lsymbols. This is
   done in [set_vs]; but in cases where the attribute is directly on the lsymbol
   term application (Tapp), the substitution may not work resulting in an error
   of the transformation. That's why we check for equality modulo attributes and
   then copy attributes back on the term again. *)
let rec t_replace t1 t2 t =
  if t_equal t t1 then t_attr_copy t t2 else t_map (t_replace t1 t2) t

let vs_of_ls = Wls.memoize 7 (fun ({ls_name = id} as ls) ->
  let attrs = Sattr.remove Inlining.intro_attr id.id_attrs in
  let id = id_fresh ~attrs ?loc:id.id_loc id.id_string in
  create_vsymbol id (Opt.get ls.ls_value))

let rec generalize hd =
  match hd.Task.task_decl.Theory.td_node with
  | Theory.Decl {d_node = Dprop (Pgoal,pr,f)} ->
      let pl, task = apply_prev generalize hd in
      if pl = [] then [], Some hd else
      let expl = get_expls f in
      let set_vs vs ls f =
        t_replace (t_app ls [] ls.ls_value) (t_var vs) f in
      let rewind (vl,f) d = match d.d_node with
        | Dparam ls ->
            let v = vs_of_ls ls in
            v::vl, set_vs v ls f
        | Dlogic [ls,ld] ->
            let f = t_forall_close vl [] f in
            let v = vs_of_ls ls in
            let f = set_vs v ls f in
            let _, h = Decl.open_ls_defn ld in
            [], t_let_close v h f
        | Dprop (Paxiom,_,h) ->
            let f = t_forall_close vl [] f in
            [], t_implies h f
        | _ -> assert false (* never *) in
      let vl, f = List.fold_left rewind ([],f) pl in
      let f = t_forall_close vl [] f in
      let f = if Sattr.is_empty expl then f else
              t_attr_add  (Sattr.min_elt expl) f in
      [], Task.add_decl task (create_prop_decl Pgoal pr f)
  | Theory.Decl ({d_node =
      ( Dparam ({ls_args = []; ls_value = Some _} as ls)
      | Dlogic [{ls_args = []; ls_value = Some _} as ls, _])} as d)
    when Sattr.mem Inlining.intro_attr ls.ls_name.id_attrs ->
      let pl, task = apply_prev generalize hd in
      d::pl, Task.add_meta task meta_intro_ls [Theory.MAls ls]
  | Theory.Decl ({d_node = Dprop (Paxiom, pr, _)} as d)
    when Sattr.mem Inlining.intro_attr pr.pr_name.id_attrs ->
      let pl, task = apply_prev generalize hd in
      d::pl, Task.add_meta task meta_intro_pr [Theory.MApr pr]
  (* We only reattach the local premises right before the goal.
     On the first non-local premise, we ignore the accumulator
     and return the original task. We make an exception for
     metas, as they are not checked against the known_map *)
  | Theory.Meta _ ->
      let pl, task = apply_prev generalize hd in
      pl, Task.add_tdecl task hd.Task.task_decl
  | _ ->
      [], Some hd

let generalize_intro = Trans.store (apply_head generalize)

let () = Trans.register_transform "generalize_introduced" generalize_intro
  ~desc:"Move@ the@ premises@ introduced@ by@ \"introduce_premises\"@ back@ \
         into@ the@ goal."


(** Destruction of existential quantifiers in axioms.
    Contributed by Nicolas Jeannerod [niols@niols.fr] *)
let rec eliminate_exists_aux pr t =
  match t.t_node with
  | Tquant (Texists, q) ->
     let vsl, _, t' = t_open_quant q in
     let intro_var subst vs =
       let id = id_clone ~attrs:intro_attrs vs.vs_name in
       let ls =
         create_lsymbol id [] (Some vs.vs_ty)
       in
       Mvs.add vs (fs_app ls [] vs.vs_ty) subst, create_param_decl ls
     in
     let subst, dl = Lists.map_fold_left intro_var Mvs.empty vsl in
     let t' = t_subst subst t' in
     let t = t_attr_copy t t' in
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

let subst_filter ls =
  Sattr.mem Inlining.intro_attr ls.ls_name.id_attrs &&
  not (relevant_for_counterexample ls.ls_name)

let simplify_intros =
  Trans.compose introduce_premises
                (Subst.subst_filtered ~subst_proxy:false subst_filter)

let split_vc =
  Trans.compose_l
    (Trans.compose generalize_intro Split_goal.split_goal_right)
    (Trans.singleton simplify_intros)

let () = Trans.register_transform_l
           "split_vc" split_vc
           ~desc:"The@ recommended@ splitting@ transformation@ to@ apply@ \
              on@ VCs@ generated@ by@ WP@ (split_goal_right@ followed@ \
              by@ introduce_premises@ followed@ by@ subst_all)."
