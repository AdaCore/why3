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

let plugins = Queue.create ()

let add_plugin x = Queue.add x plugins

let option_list = Arg.align [
  (* "--libdir", Arg.String (set_oref libdir), *)
  (* "<dir> set the lib directory ($WHY3LIB)"; *)
  (* "--datadir", Arg.String (set_oref datadir), *)
  (* "<dir> set the data directory ($WHY3DATA)"; *)
  "--conf_file", Arg.String (set_oref conf_file),
  "<file> use this configuration file, create it if it doesn't exist
($WHY_CONFIG), otherwise use the default one";
  "--autodetect-provers", Arg.Set auto,
  " autodetect the provers in the $PATH";
  "--install-plugin", Arg.String add_plugin,
  "install a plugin to the actual libdir";
]

let anon_file _ = Arg.usage option_list usage_msg; exit 1

let install_plugin main p =
  begin match Plugin.check_extension p with
    | Plugin.Extbad -> eprintf "Unknown extension (.cmo|.cmxs) : %s@." p;exit 1
    | Plugin.Extother ->
      eprintf "This plugin %s will not be used with this kind of compilation@."
        p
    | Plugin.Extgood -> ()
  end;
  let base = Filename.basename p in
  let pluginsdir = Whyconf.pluginsdir main in
  Sysutil.copy_file p (Filename.concat pluginsdir base);
  Whyconf.add_plugin main (Filename.chop_extension base)

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
  let main = Queue.fold install_plugin main plugins in
  let config = set_main config main in
  let conf_file = get_conf_file config in
  let conf_file_doesnt_exist = not (Sys.file_exists conf_file) in
  if conf_file_doesnt_exist then
    printf "Config file %s doesn't exist, \
 so autodetection is automatically triggered@." conf_file;
  let config =
    if !auto || conf_file_doesnt_exist
    then Autodetection.run_auto_detection config
    else config in
  printf "Save config to %s@." conf_file;
  save_config config
