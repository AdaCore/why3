(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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
open Task

let abstraction (keep : lsymbol -> bool) =
  let term_table = Hterm_alpha.create 257 in
  let fmla_table = Hterm_alpha.create 257 in
  let extra_decls = ref [] in

  let rec abstract_term t : term =
    match t.t_node with
    | Tconst _ | Tapp(_,[]) -> t
    | Tapp(ls,_) when keep ls ->
        t_map abstract_term abstract_fmla t
    | _ ->
        let (ls, tabs) = try Hterm_alpha.find term_table t with Not_found ->
          let ls = create_lsymbol (id_fresh "abstr") [] t.t_ty in
          let tabs = e_app ls [] t.t_ty in
          Hterm_alpha.add term_table t (ls, tabs);
          ls, tabs in
        extra_decls := ls :: !extra_decls;
        tabs

  and abstract_fmla f =
    match f.t_node with
    | Ftrue | Ffalse -> f
    | Fnot _ | Fbinop _ ->
        t_map abstract_term abstract_fmla f
    | Tapp(ls,_) when keep ls ->
        t_map abstract_term abstract_fmla f
    | _ ->
        let (ls, fabs) = try Hterm_alpha.find fmla_table f with Not_found ->
          let ls = create_psymbol (id_fresh "abstr") [] in
          let fabs = f_app ls [] in
          Hterm_alpha.add fmla_table f (ls, fabs);
          ls, fabs in
        extra_decls := ls :: !extra_decls;
        fabs in

  let abstract_decl (d : decl) : decl list =
    let d = decl_map abstract_term abstract_fmla d in
    let l = List.fold_left
      (fun acc ls -> create_logic_decl [ls,None] :: acc)
      [d] !extra_decls in
    extra_decls := []; l in

  Trans.decl abstract_decl None
