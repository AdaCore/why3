(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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
open Why3
open Util
open Whyconf

let usage_msg =
  sprintf "Usage: %s [options]\n
  Environment variables WHY3LIB, WHY3DATA, and WHY3CONFIG
  can be set to change the default paths.@."
    (Filename.basename Sys.argv.(0))

let version_msg = sprintf
  "Why3 configuration utility, version %s (build date: %s)"
  Config.version Config.builddate

(* let libdir = ref None *)
(* let datadir = ref None *)
let conf_file = ref None
let autoprovers = ref false
let autoplugins = ref false
let opt_version = ref false

let opt_list_prover_ids = ref false

let save = ref true

let set_oref r = (fun s -> r := Some s)

let prover_bins = Queue.create ()

let add_prover arg =
  let res =
    try
      let index = String.index arg ':' in
      (String.sub arg 0 index),
      (String.sub arg (index+1) (String.length arg - (index + 1)))
    with Not_found ->
      eprintf "Error: provide a path to the prover binary.@.";
      exit 1
  in
  Queue.add res prover_bins

let plugins = Queue.create ()
let add_plugin x = Queue.add x plugins

let option_list = Arg.align [
  (* "--libdir", Arg.String (set_oref libdir), *)
  (* "<dir> set the lib directory ($WHY3LIB)"; *)
  (* "--datadir", Arg.String (set_oref datadir), *)
  (* "<dir> set the data directory ($WHY3DATA)"; *)
  "-C", Arg.String (set_oref conf_file),
  "<file> Config file to create";
  "--config", Arg.String (set_oref conf_file),
      " same as -C";
  "--detect-provers", Arg.Set autoprovers,
  " Search for provers in $PATH";
  "--detect-plugins", Arg.Set autoplugins,
  " Search for plugins in the default library directory";
  "--detect", Arg.Unit (fun () -> autoprovers := true; autoplugins := true),
  " Search for both provers and plugins";
  "--add-prover", Arg.String add_prover,
  "<id>:<file> Add a new prover executable";
  "--list-prover-ids", Arg.Set opt_list_prover_ids,
  " List known prover families";
  "--install-plugin", Arg.String add_plugin,
  "<file> Install a plugin to the actual libdir";
  "--dont-save", Arg.Clear save,
  " Do not modify the config file";
  Debug.Opt.desc_debug_list;
  Debug.Opt.desc_debug_all;
  Debug.Opt.desc_debug;
  "--version", Arg.Set opt_version,
  " Print version information"
]

let anon_file _ = Arg.usage option_list usage_msg; exit 1

let add_prover_binary config (id,file) =
  Autodetection.add_prover_binary config id file

let install_plugin main p =
  begin match Plugin.check_plugin p with
    | Plugin.Plubad ->
        Debug.dprintf Plugin.debug "Unknown extension (.cmo|.cmxs) : %s@." p;
        raise Exit
    | Plugin.Pluother ->
        Debug.dprintf Plugin.debug
          "The plugin %s cannot be used with this kind of compilation@." p;
        raise Exit
    | Plugin.Plufail exn ->
        eprintf "The plugin %s dynlink failed :@.%a@."
          p Exn_printer.exn_printer exn;
        raise Exit
    | Plugin.Plugood ->
        eprintf "== Found %s ==@." p
  end;
  let base = Filename.basename p in
  let plugindir = Whyconf.pluginsdir main in
  if not (Sys.file_exists plugindir) then begin
    eprintf "Error: plugin directory %s not found.@." plugindir;
    raise Exit
  end;
  let target = (Filename.concat plugindir base) in
  if p <> target then Sysutil.copy_file p target;
  Whyconf.add_plugin main (Filename.chop_extension target)

let plugins_auto_detection config =
  let main = get_main config in
  let main = set_plugins main [] in
  let dir = Whyconf.pluginsdir main in
  let files = Sys.readdir dir in
  let fold main p =
    if p.[0] == '.' then main else
    let p = Filename.concat dir p in
    try
        install_plugin main p
    with Exit -> main
  in
  let main = Array.fold_left fold main files in
  set_main config main

let main () =
  (** Parse the command line *)
  Arg.parse option_list anon_file usage_msg;

  let opt_list = ref false in
  if !opt_version then begin
    opt_list := true;
    printf "%s@." version_msg
  end;

  (** Debug flag *)
  Debug.Opt.set_flags_selected ();

  if !opt_list_prover_ids then begin
    opt_list := true;
    printf "@[<hov 2>Known prover families:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Autodetection.list_prover_ids ()))
  end;

  opt_list :=  Debug.Opt.option_list () || !opt_list;
  if !opt_list then exit 0;

  (** Main *)
  let config =
    try
      read_config !conf_file
    with
      | Rc.CannotOpen (f, s)
      | Whyconf.ConfigFailure (f, s) ->
         eprintf "warning: cannot read config file %s:@\n  %s@." f s;
         autoprovers := true;
         autoplugins := true;
         default_config f
  in
  let main = get_main config in
  (* let main = option_apply main (fun d -> {main with libdir = d})
     !libdir in *)
  (* let main = option_apply main (fun d -> {main with datadir = d})
     !datadir in *)
  let main = try Queue.fold install_plugin main plugins with Exit -> exit 1 in
  let config = set_main config main in
  let config =
    try Queue.fold add_prover_binary config prover_bins with Exit -> exit 1 in

  let conf_file = get_conf_file config in
  if not (Sys.file_exists conf_file) then begin
    autoprovers := true;
    autoplugins := true;
  end;
  let config =
    if !autoprovers
    then Autodetection.run_auto_detection config
    else config
  in
  let config =
    if !autoplugins
    then plugins_auto_detection config
    else config
  in
  if !save then begin
    printf "Save config to %s@." conf_file;
    save_config config
  end

let () =
  try
    main ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

