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

open Format
open Why
open Util
open Whyconf

let usage_msg =
  sprintf "Usage: [WHY3LIB=... WHY3DATA=... %s [options]@.\t\
$WHY3LIB and $WHYDATA are used only when a configuration file is created"
    (Filename.basename Sys.argv.(0))

(* let libdir = ref None *)
(* let datadir = ref None *)
let conf_file = ref None
let auto = ref false

let set_oref r = (fun s -> r := Some s)

let option_list = Arg.align [
  (* "--libdir", Arg.String (set_oref libdir), *)
  (* "<dir> set the lib directory ($WHY3LIB)"; *)
  (* "--datadir", Arg.String (set_oref datadir), *)
  (* "<dir> set the data directory ($WHY3DATA)"; *)
  "--conf_file", Arg.String (set_oref conf_file),
  "<file> use this configuration file, create it if it doesn't exist
($WHY_CONFIG), otherwise use the default one";
  "--autodetect-provers", Arg.Set auto,
  " autodetect the provers in the $PATH"]

let anon_file _ = Arg.usage option_list usage_msg; exit 1

let () =
  Arg.parse option_list anon_file usage_msg;
  let config =
    try read_config !conf_file
    with Not_found ->
      let conf_file = match !conf_file with
        | None -> Sys.getenv "WHY_CONFIG"
        | Some f -> f in
      default_config conf_file in
  let main = get_main config in
  (* let main = option_apply main (fun d -> {main with libdir = d})
     !libdir in *)
  (* let main = option_apply main (fun d -> {main with datadir = d})
     !datadir in *)
  let config = set_main config main in
  let config =
    if !auto
    then Autodetection.run_auto_detection config
    else config in
  printf "Save config to %s@." (get_conf_file config);
  save_config config
