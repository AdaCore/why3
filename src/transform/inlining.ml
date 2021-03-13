(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
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
open Theory
open Task

let intro_attr = create_attribute "introduced"
let inline_trivial_attr = create_attribute "inline:trivial"

let meta_get_counterexmp =
  Theory.register_meta_excl "get_counterexmp" [Theory.MTstring]
  ~desc:"Set@ when@ counter-example@ should@ be@ get."

let get_counterexmp task =
  let ce_meta = Task.find_meta_tds task meta_get_counterexmp in
  not (Theory.Stdecl.is_empty ce_meta.tds_set)

let rec relocate loc t =
  t_map (relocate loc) (t_attr_set ?loc t.t_attrs t)

let t_unfold loc env fs tl ty =
  match Mls.find_opt fs env with
  | None ->
      t_app fs tl ty
  | Some (vl,e) ->
      let add (mt,mv) x y = ty_match mt x.vs_ty (t_type y), Mvs.add x y mv in
      let (mt,mv) = List.fold_left2 add (Ty.Mtv.empty, Mvs.empty) vl tl in
      let mt = oty_match mt e.t_ty ty in
      t_ty_subst mt mv (relocate loc e)

(* inline every symbol *)

let rec t_replace_all env t =
  let t = t_map (t_replace_all env) t in
  match t.t_node with
  | Tapp (fs,tl) -> t_attr_copy t (t_unfold t.t_loc env fs tl t.t_ty)
  | _ -> t

(* inline the top-most symbol *)

let rec f_replace_top env f = match f.t_node with
  | Tapp (ps,_) when ls_equal ps ps_equ ->
      t_map (f_replace_top env) f
  | Tapp (ls,tl) ->
      t_attr_copy f (t_unfold f.t_loc env ls tl f.t_ty)
  | _ when f.t_ty = None ->
      TermTF.t_map (fun t -> t) (f_replace_top env) f
  | _ ->
      f

(* treat a declaration *)

let fold in_goal notls notdef d (env, task) =
  let d = match d.d_node with
    | Dprop (Pgoal,_,_) when in_goal ->
        decl_map (f_replace_top env) d
    | _ when in_goal ->
        d
    | _ ->
        decl_map (t_replace_all env) d
  in
  match d.d_node with
    | Dlogic [ls,ld]
      when not (Sid.mem ls.ls_name (get_decl_syms d) || notls ls) ->
        let vl,e = open_ls_defn ld in
        let attrs = Sattr.union e.t_attrs ls.ls_name.id_attrs in
        let e_ls_attrs = t_attr_set ?loc:e.t_loc attrs e in
        if notdef e_ls_attrs then env, Task.add_decl task d
        else Mls.add ls (vl,e) env,
             if in_goal then Task.add_decl task d else task
    | _ ->
        env, Task.add_decl task d

let fold in_goal notls notdef task_hd (env, task) =
  match task_hd.task_decl.td_node with
    | Decl d ->
        fold in_goal notls notdef d (env, task)
    | _ ->
        env, add_tdecl task task_hd.task_decl

(* transformations *)

let meta = Theory.register_meta "inline:no" [Theory.MTlsymbol]
  ~desc:"Disallow@ the@ inlining@ of@ the@ given@ function/predicate@ symbol."

let t ?(use_meta=true) ?(in_goal=false) ~notls ~notdef =
  Trans.bind (Trans.store get_counterexmp) (fun for_counterexample ->
    let trans notls =
      Trans.fold_map (fold in_goal notls notdef) Mls.empty None in
    if use_meta then
      Trans.on_tagged_ls meta (fun sls ->
        let notls ls = Sls.mem ls sls || notls ~for_counterexample ls in
        trans notls)
    else
      trans (notls ~for_counterexample))

let all =
  t ~use_meta:true ~in_goal:false ~notdef:Util.ffalse
    ~notls:(fun ~for_counterexample:_ _ -> false)

let goal =
  t ~use_meta:true ~in_goal:true ~notdef:Util.ffalse
    ~notls:(fun ~for_counterexample:_ _ -> false)

(* inline_trivial *)

let trivial tl =
  let add vs t = match t.t_node with
    | Tvar v when Mvs.mem v vs -> raise Util.FoldSkip
    | Tvar v -> Svs.add v vs
    | Teps _ -> raise Util.FoldSkip
    | _ when t_closed t -> vs
    | _ -> raise Util.FoldSkip
  in
  try ignore (List.fold_left add Svs.empty tl); true
  with Util.FoldSkip -> false

let notdef t = match t.t_node with
  | _ when Sattr.mem inline_trivial_attr t.t_attrs -> false
  | Tvar _ | Tconst _ -> false
  | Ttrue  | Tfalse   -> false
  | Tapp (_,tl) -> not (trivial tl)
  | _ -> true

let trivial =
  let notls ~for_counterexample ls =
    (* do not inline things like `let result = ... in ...`
       when counterexamples are wanted. These are recognized
       as having the attribute `introduced` *)
    for_counterexample && ls.ls_args = [] &&
      Sattr.mem intro_attr ls.ls_name.id_attrs in
  t ~use_meta:true ~in_goal:false ~notls ~notdef

let () =
  Trans.register_transform "inline_all" all
    ~desc:"Inline@ non-recursive@ definitions.";
  Trans.register_transform "inline_goal" goal
    ~desc:"Same@ as@ 'inline_all', but@ only@ inline in@ goals.";
  Trans.register_transform "inline_trivial" trivial
    ~desc:"Inline@ trivial@ definitions@ like@ @[f(x,y) = g(y,x,0)@]. \
           Add@ the@ [@@inline:trivial]@ attribute@ to@ force@ inlining."
