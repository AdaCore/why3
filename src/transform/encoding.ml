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

type enco_opt =
    { meta : meta;
      default : string;
      table : (string,env -> task trans) Hashtbl.t}

let enco_opt s d =
  let table = Hashtbl.create 17 in
  { meta = register_meta_excl (Format.sprintf "enco_%s" s) [MTstring];
    table = table;
    default = d},
  Hashtbl.add table

let select_opt,register_enco_select = enco_opt "select" "kept"
let kept_opt,register_enco_kept = enco_opt "kept" "bridge"
let poly_opt,register_enco_poly = enco_opt "poly" "decorate"

let poly_smt_opt = poly_opt
let poly_tptp_opt = poly_opt

let enco_gen opt env =
  Trans.on_meta_excl opt.meta (fun alo ->
    let s = match alo with
      | None -> opt.default
      | Some [MAstr s] -> s
      | _ -> assert false in
    try
      Trans.named s ((Hashtbl.find opt.table s) env)
    with Not_found -> failwith
      (Format.sprintf "encoding : %s wrong argument %s" opt.meta.meta_name s))

let print_kept = print_meta debug meta_kept
let enco_select env = compose (enco_gen select_opt env) print_kept
let enco_kept = enco_gen kept_opt
let enco_poly_smt = enco_gen poly_smt_opt
let enco_poly_tptp = enco_gen poly_tptp_opt

let forbid_for_explicit =
  Encoding_enumeration.forbid_enumeration
    "explicit is unsound in presence of this finite type"

let maybe_forbid_enumeration =
  Trans.on_meta_excl poly_smt_opt.meta (fun alo ->
    let s = match alo with
      | None -> poly_smt_opt.default
      | Some [MAstr s] -> s
      | _ -> assert false in
    if s = "explicit"
    then forbid_for_explicit
    else Trans.identity)

let forbid_enumeration =
  Trans.on_meta_excl poly_smt_opt.meta (fun alo ->
    let s = match alo with
      | None -> poly_smt_opt.default
      | Some [MAstr s] -> s
      | _ -> assert false in
    if s = "explicit"
    then forbid_for_explicit
    else Encoding_enumeration.encoding_enumeration)


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
  compose monomorphise_goal
    (compose maybe_forbid_enumeration
       (compose (enco_select env)
          (compose (enco_kept env) (enco_poly_smt env))))

let encoding_tptp env =
  compose monomorphise_goal
    (compose forbid_enumeration
       (compose (enco_select env)
          (compose (enco_kept env) (enco_poly_tptp env))))

let () =
  register_env_transform "encoding_smt" encoding_smt;
  register_env_transform "encoding_tptp" encoding_tptp
