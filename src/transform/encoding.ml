(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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
open Encoding_enumeration

let meta_kept = register_meta "encoding : kept" [MTtysymbol]

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

let enco_gen opt env =
  Trans.on_meta opt.meta (fun tds ->
    let s = match get_meta_excl opt.meta tds with
      | None -> opt.default
      | Some [MAstr s] -> s
      | _ -> assert false in
    try
      (Hashtbl.find opt.table s) env
    with Not_found -> failwith
      (Format.sprintf "encoding : %s wrong argument %s"
         (meta_name opt.meta) s))

let enco_select = enco_gen select_opt
let enco_kept = enco_gen kept_opt
let enco_poly = enco_gen poly_opt

let encoding_smt env =
  compose (enco_select env)
  (compose (enco_kept env) (enco_poly env))

let encoding_tptp env = compose (encoding_smt env) encoding_enumeration

let () =
  register_env_transform "encoding_smt" encoding_smt;
  register_env_transform "encoding_tptp" encoding_tptp
