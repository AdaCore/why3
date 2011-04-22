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

open Env
open Theory
open Task
open Trans

let meta_kept = register_meta "encoding : kept" [MTty]
let meta_kept_array = register_meta "encoding : kept_array" [MTty]
let meta_base = register_meta_excl "encoding : base" [MTtysymbol]

let debug = Debug.register_flag "encoding"

let select_pr = Trans.create_private_register "enco_select" "kept"
let kept_pr = Trans.create_private_register "enco_kept" "bridge"
let poly_pr = Trans.create_private_register "enco_poly" "decorate"

let poly_smt_pr = poly_pr
let poly_tptp_pr = poly_pr

let print_kept = print_meta debug meta_kept
let enco_select env =
  compose (apply_private_register_env select_pr env) print_kept


open Ty
open Term

let ty_all_quant =
  let rec add_vs s ty = match ty.ty_node with
    | Tyvar vs -> Stv.add vs s
    | _ -> ty_fold add_vs s ty in
  f_ty_fold add_vs Stv.empty

let monomorphise_goal =
  Trans.goal (fun pr f ->
    let stv = ty_all_quant f in
    let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
      let ts = create_tysymbol (Ident.id_clone tv.tv_name) [] None in
      Mtv.add tv (ty_app ts []) mty,ts::ltv) stv (Mtv.empty,[]) in
    let f = f_ty_subst mty Mvs.empty f in
    let acc = [Decl.create_prop_decl Decl.Pgoal pr f] in
    let acc = List.fold_left
      (fun acc ts -> (Decl.create_ty_decl [ts,Decl.Tabstract]) :: acc)
      acc ltv in
    acc)

let encoding_smt env =
  Trans.seq [
    monomorphise_goal;
    enco_select env;
    apply_private_register_env kept_pr env;
    apply_private_register_env poly_smt_pr env]

let encoding_tptp env =
  Trans.seq [
    monomorphise_goal;
    enco_select env;
    apply_private_register_env kept_pr env;
    apply_private_register_env poly_tptp_pr env;
    Encoding_enumeration.encoding_enumeration]

let () =
  register_env_transform "encoding_smt" encoding_smt;
  register_env_transform "encoding_tptp" encoding_tptp
