(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Term
open Decl

let rec lift_f acc t = match t.t_node with
  | (Tapp (ps, [t1; {t_node = Teps fb}])
  | Tapp (ps, [{t_node = Teps fb}; t1]))
    when ls_equal ps ps_equ ->
      let vs, f = t_open_bound fb in
      lift_f acc (t_let_close_simp vs t1 f)
  | Teps fb ->
      let vl = Mvs.keys (t_vars t) in
      let vs, f = t_open_bound fb in
      let (abst,axml), f = lift_f acc f in
      let tyl = List.map (fun x -> x.vs_ty) vl in
      let ls = create_fsymbol (id_clone vs.vs_name) tyl vs.vs_ty in
      let t = t_app ls (List.map t_var vl) t.t_ty in
      let f = t_forall_close_merge vl (t_subst_single vs t f) in
      let id = id_derive (vs.vs_name.id_string ^ "_def") vs.vs_name in
      let ax = create_prop_decl Paxiom (create_prsymbol id) f in
      (create_param_decl ls :: abst, ax :: axml), t
  | _ ->
      t_map_fold lift_f acc t

let lift_l (acc,dl) (ls,ld) =
  let vl, t, close = open_ls_defn_cb ld in
  match t.t_node with
  | Teps fb ->
      let vs, f = t_open_bound fb in
      let (abst,axml), f = lift_f acc f in
      let t = t_app ls (List.map t_var vl) t.t_ty in
      let f = t_forall_close_merge vl (t_subst_single vs t f) in
      let id = id_derive (ls.ls_name.id_string ^ "_def") ls.ls_name in
      let ax = create_prop_decl Paxiom (create_prsymbol id) f in
      (create_param_decl ls :: abst, ax :: axml), dl
  | _ ->
      let acc, t = lift_f acc t in
      acc, close ls vl t :: dl

let lift_d d = match d.d_node with
  | Dlogic dl ->
      let (abst,axml), dl = List.fold_left lift_l (([],[]),[]) dl in
      if dl = [] then List.rev_append abst (List.rev axml) else
      let d = create_logic_decl (List.rev dl) in
      let add_ax (axml1, axml2) ax =
        if Sid.disjoint ax.d_syms d.d_news
        then ax :: axml1, axml2 else axml1, ax :: axml2 in
      let axml1, axml2 = List.fold_left add_ax ([],[]) axml in
      List.rev_append abst (axml1 @ d :: axml2)
  | _ ->
      let (abst,axml), d = decl_map_fold lift_f ([],[]) d in
      List.rev_append abst (List.rev_append axml [d])

let eliminate_epsilon = Trans.decl lift_d None

let () = Trans.register_transform "eliminate_epsilon" eliminate_epsilon
  ~desc:"Eliminate@ lambda-terms@ and@ other@ comprehension@ forms."
