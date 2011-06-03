(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
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
open Decl
open Theory
open Task
open Trans

let debug = Debug.register_flag "encoding"

let meta_kept = register_meta      "encoding : kept" [MTty]
let meta_base = register_meta_excl "encoding : base" [MTtysymbol]

let meta_select_kept = register_meta_excl "select_kept" [MTstring]
let meta_enco_kept   = register_meta_excl "enco_kept"   [MTstring]
let meta_enco_poly   = register_meta_excl "enco_poly"   [MTstring]

let def_enco_select_smt  = "none"
let def_enco_kept_smt    = "bridge"
let def_enco_poly_smt    = "decorate"

let def_enco_select_tptp = "none"
let def_enco_kept_tptp   = "bridge"
let def_enco_poly_tptp   = "decorate"

let ft_select_kept = ((Hashtbl.create 17) : (Env.env,Sty.t) Trans.flag_trans)
let ft_enco_kept   = ((Hashtbl.create 17) : (Env.env,task)  Trans.flag_trans)
let ft_enco_poly   = ((Hashtbl.create 17) : (Env.env,task)  Trans.flag_trans)

let monomorphise_goal = Trans.goal (fun pr f ->
  let stv = t_ty_freevars Stv.empty f in
  if Stv.is_empty stv then [create_prop_decl Pgoal pr f] else
  let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
    let ts = create_tysymbol (id_clone tv.tv_name) [] None in
    Mtv.add tv (ty_app ts []) mty, ts::ltv) stv (Mtv.empty,[]) in
  let f = t_ty_subst mty Mvs.empty f in
  List.fold_left
    (fun acc ts -> create_ty_decl [ts,Tabstract] :: acc)
    [create_prop_decl Pgoal pr f] ltv)

let select_kept def env =
  let select = Trans.on_flag meta_select_kept ft_select_kept def env in
  let trans task =
    let sty = Trans.apply select task in
    let create_meta_ty ty = create_meta meta_kept [MAty ty] in
    let decls = Sty.fold (flip $ cons create_meta_ty) sty [] in
    Trans.apply (Trans.add_tdecls decls) task
  in
  Trans.store trans

let encoding_smt env = Trans.seq [
  monomorphise_goal;
  select_kept def_enco_select_smt env;
  Trans.print_meta debug meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_smt env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_smt env]

let encoding_tptp env = Trans.seq [
  monomorphise_goal;
  select_kept def_enco_select_tptp env;
  Trans.print_meta debug meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_tptp env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_tptp env;
  Encoding_enumeration.encoding_enumeration]

let () = register_env_transform "encoding_smt" encoding_smt
let () = register_env_transform "encoding_tptp" encoding_tptp

