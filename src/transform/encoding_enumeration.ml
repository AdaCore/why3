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

open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl

let meta_enum = Eliminate_algebraic.meta_enum

type tenv = {
  enum  : Sts.t;
  projs : lsymbol Hts.t
}

let add_proj tenv ts =
  try Hts.find tenv.projs ts with Not_found ->
  let id = id_fresh ("enum_proj_" ^ ts.ts_name.id_string) in
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let fs = create_fsymbol id [ty] ty in
  Hts.add tenv.projs ts fs;
  fs

let proj tenv t ty = match ty.ty_node with
  | Tyapp (ts,_) when Sts.mem ts tenv.enum ->
      let fs = Hts.find tenv.projs ts in
      t_app fs [t] t.t_ty
  | _ -> t

let proj tenv t = match t.t_node with
  | Tapp (ls,_) ->
      proj tenv t (of_option ls.ls_value)
  | Tvar _ | Tconst _ | Teps _ ->
      proj tenv t t.t_ty
  | Tif _  | Tcase _  | Tlet _ ->
      t

let rec rewrite_term tenv t = match t.t_node with
  | Tapp (fs,tl) ->
      let pin t = proj tenv (rewrite_term tenv t) in
      t_app fs (List.map pin tl) t.t_ty
  | Tcase _ ->
      Printer.unsupportedTerm t "use eliminate_algebraic"
  | _ -> t_map (rewrite_term tenv) (rewrite_fmla tenv) t

and rewrite_fmla tenv f = match f.f_node with
  | Fapp (ps,tl) ->
      let pin t = proj tenv (rewrite_term tenv t) in
      f_app ps (List.map pin tl)
  | Fcase _ ->
      Printer.unsupportedFmla f "use eliminate_algebraic"
  | _ -> f_map (rewrite_term tenv) (rewrite_fmla tenv) f

let decl tenv d = match d.d_node with
  | Dtype tl ->
      let add acc t = match t with
        | ts, Tabstract when Sts.mem ts tenv.enum ->
            let ls = add_proj tenv ts in
            let acc = create_ty_decl [t] :: acc in
            create_logic_decl [ls, None] :: acc
        | _, Tabstract ->
            create_ty_decl [t] :: acc
        | _ ->
            Printer.unsupportedDecl d "use eliminate_algebraic"
      in
      List.rev (List.fold_left add [] tl)
  | _ ->
      [decl_map (rewrite_term tenv) (rewrite_fmla tenv) d]

let encoding_enumeration =
  let projs = Hts.create 17 in
  Trans.on_tagged_ts meta_enum (fun enum ->
    let tenv = { enum = enum ; projs = projs } in
    Trans.decl (decl tenv) None)

let () = Trans.register_transform "encoding_enumeration" encoding_enumeration

