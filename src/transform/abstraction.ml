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


open Ident
open Term
open Decl

let abstraction (keep : lsymbol -> bool) =
  let term_table = Hterm_nt_na.create 257 in
  let extra_decls = ref [] in

  let rec abstract t : term =
    match t.t_node with
    | Tconst _ | Tapp(_,[]) | Ttrue | Tfalse -> t
    | Tapp(ls,_) when keep ls ->
        t_map abstract t
    | Tnot _ | Tbinop _ ->
        t_map abstract t
    | _ ->
        let t = t_attr_set Sattr.empty t in
        let (ls, tabs) = try Hterm_nt_na.find term_table t with Not_found ->
          let ls = create_lsymbol (id_fresh "abstr") [] t.t_ty in
          let tabs = t_app ls [] t.t_ty in
          Hterm_nt_na.add term_table t (ls, tabs);
          ls, tabs in
        extra_decls := ls :: !extra_decls;
        tabs in

  let abstract_decl (d : decl) : decl list =
    let d = decl_map abstract d in
    let l = List.fold_left
      (fun acc ls -> create_param_decl ls :: acc)
      [d] !extra_decls in
    extra_decls := []; l in

  Trans.decl abstract_decl None
