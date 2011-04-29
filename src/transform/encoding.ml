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
open Ty
open Task
open Trans
open Term

let debug = Debug.register_flag "encoding"

let meta_lsinst   = Encoding_distinction.meta_lsinst
let meta_kept   = Encoding_distinction.meta_kept
let meta_lskept = register_meta "encoding : lskept"    [MTlsymbol]
let meta_base   = register_meta_excl "encoding : base" [MTtysymbol]


let meta_select_lsinst   = register_meta_excl "select_inst"     [MTstring]
let meta_select_kept     = register_meta_excl "select_kept"     [MTstring]
let meta_select_lskept   = register_meta_excl "select_lskept"   [MTstring]
let meta_completion_mode = register_meta_excl "completion_mode" [MTstring]

let meta_enco_kept       = register_meta_excl "enco_kept"       [MTstring]
let meta_enco_poly       = register_meta_excl "enco_poly"       [MTstring]


let def_enco_select_smt = "kept"
let def_enco_kept_smt   = "bridge"
let def_enco_poly_smt   = "decorate"

let def_enco_select_tptp = "kept"
let def_enco_kept_tptp   = "bridge"
let def_enco_poly_tptp   = "decorate"


let ft_select_lsinst    = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)
let ft_select_kept      = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)
let ft_select_lskept    = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)
let ft_completion_mode  = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)

let ft_enco_kept   = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)
let ft_enco_poly   = ((Hashtbl.create 17) : (env,task) Trans.flag_trans)


let monomorphise_goal =
  Trans.goal (fun pr f ->
    let stv = f_ty_freevars Stv.empty f in
    let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
      let ts = create_tysymbol (Ident.id_clone tv.tv_name) [] None in
      Mtv.add tv (ty_app ts []) mty,ts::ltv) stv (Mtv.empty,[]) in
    let f = f_ty_subst mty Mvs.empty f in
    let acc = [Decl.create_prop_decl Decl.Pgoal pr f] in
    let acc = List.fold_left
      (fun acc ts -> (Decl.create_ty_decl [ts,Decl.Tabstract]) :: acc)
      acc ltv in
    acc)


let lsymbol_distinction =
  Trans.compose (Trans.print_meta debug meta_lsinst)
    Encoding_distinction.lsymbol_distinction

let phase0 env = Trans.seq [
  Trans.on_flag meta_select_lsinst   ft_select_lsinst   "nothing" env;
  Trans.on_flag meta_select_kept     ft_select_kept     "nothing" env;
  Trans.on_flag meta_select_lskept   ft_select_lskept   "nothing" env;
  Trans.on_flag meta_completion_mode ft_completion_mode "nothing" env;
  lsymbol_distinction;
]


let encoding_smt env = Trans.seq [
  monomorphise_goal;
  phase0 env;
  Trans.print_meta debug meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_smt env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_smt env]

let encoding_tptp env = Trans.seq [
  monomorphise_goal;
  phase0 env;
  Trans.print_meta debug meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_tptp env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_tptp env;
  Encoding_enumeration.encoding_enumeration]

let () =
  register_env_transform "encoding_smt" encoding_smt;
  register_env_transform "encoding_tptp" encoding_tptp
