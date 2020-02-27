(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Whyconf

(* let libdir = ref None *)
(* let datadir = ref None *)
let conf_file = ref None
let autoprovers = ref false
let autoplugins = ref false
let partial_config = ref true
let resetloadpath = ref false

(* When no arguments are given, activate the fallback to auto mode on error.
   true <-> fallback *)
let auto_fb = Array.length Sys.argv = 1

let opt_list_prover_families = ref false

let save = ref true

let set_oref r = (fun s -> r := Some s)

let prover_bins = Queue.create ()

let plugins = Queue.create ()
let add_plugin x = Queue.add x plugins

let spec =
  let open Getopt in
  [ Key ('C', "config"), Hnd1 (AString, set_oref conf_file),
    "<file> config file to create";
    KLong "detect-provers", Hnd0 (fun () -> autoprovers := true),
    " search for provers in $PATH";
    KLong "detect-plugins", Hnd0 (fun () -> autoplugins := true),
    " search for plugins in the default library directory";
    KLong "detect", Hnd0 (fun () -> resetloadpath := true; autoprovers := true; autoplugins := true),
    " search for both provers and plugins, and reset the default loadpath";
    KLong "add-prover", Hnd1 (APair (',', AString, (APair (',', AString, AString))),
      fun (id, (shortcut, name)) -> Queue.add (id, shortcut, name) prover_bins),
    "<id>,<shortcut>,<file> add a new prover executable";
    KLong "full-config", Hnd0 (fun () -> partial_config := false; autoprovers := true),
    " write in why3.conf the default config for provers, shortcut, strategies, and plugins, instead of loading it at startup";
    KLong "list-prover-families", Hnd0 (fun () -> opt_list_prover_families := true),
    " list known prover families";
    KLong "install-plugin", Hnd1 (AString, add_plugin),
    "<file> copy a plugin to the current library directory";
    KLong "dont-save", Hnd0 (fun () -> save := false),
    " do not modify the config file";
    Debug.NewArgs.desc_debug_list;
    Debug.NewArgs.desc_debug_all;
    Debug.NewArgs.desc_debug;
  ]

let usage () =
  Printf.eprintf
    "Usage: %s [options] \n\
     Detect provers and plugins to configure Why3.\n\
     \n%s%!"
    (Filename.basename Sys.argv.(0))
    (Getopt.format spec);
  exit 0

let spec =
  let open Why3.Getopt in
  (Key ('h', "help"), Hnd0 usage," display this help and exit") :: spec

let anon_file x = raise (Getopt.GetoptFailure (sprintf "unexpected argument: %s" x))

let add_prover_binary config (id,shortcut,file) =
  Autodetection.add_prover_binary config id shortcut file

let install_plugin main p =
  begin match Plugin.check_plugin p with
    | Plugin.Plubad ->
        Debug.dprintf Plugin.debug "Unknown extension (.cmo|.cmxs): %s@." p;
        raise Exit
    | Plugin.Pluother ->
        Debug.dprintf Plugin.debug
          "The plugin %s cannot be used with this kind of compilation@." p;
        raise Exit
    | Plugin.Plufail exn ->
        eprintf "The plugin %s dynlink failed:@.%a@."
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

(*  Activate the fallback to auto mode on error *)
let auto_fallback () =
  if auto_fb then begin
      autoprovers := true;
      autoplugins := true;
    end

let main () =
  (* Parse the command line *)
  Getopt.parse_all spec anon_file Sys.argv;

  let opt_list = ref false in
  Autodetection.is_config_command := true;

  (* Debug flag *)
  Debug.NewArgs.set_flags_selected ();

  if !opt_list_prover_families then begin
    opt_list := true;
    printf "@[<hov 2>Known prover families:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Autodetection.list_prover_families ()))
  end;

  opt_list := Debug.NewArgs.option_list () || !opt_list;
  if !opt_list then exit 0;

  (* Main *)
  let config =
    try
      read_config !conf_file
    with
      | Rc.CannotOpen (f, s)
      | Whyconf.ConfigFailure (f, s) ->
         eprintf "warning: cannot read config file %s:@\n  %s@." f s;
         auto_fallback ();
         default_config f
  in
  let main = get_main config in
  (* let main = Opt.fold main (fun d -> {main with libdir = d})
     !libdir in *)
  (* let main = Opt.fold main (fun d -> {main with datadir = d})
     !datadir in *)
  let main = try Queue.fold install_plugin main plugins with Exit -> exit 1 in
  let config = set_main config main in
  let config =
    try Queue.fold add_prover_binary config prover_bins with Exit -> exit 1 in

  let conf_file = get_conf_file config in
  if not (Sys.file_exists conf_file) then
    auto_fallback ();
  let config =
    if !resetloadpath then
      (** temporary 13/06/18 after introduction of --no-stdlib *)
      set_main config (set_loadpath (get_main config) [])
    else config
  in
  let config =
    if !autoprovers
    then
      let config = Whyconf.set_provers config (Whyconf.get_provers config) in
      let config = Whyconf.set_load_default_config !partial_config config in
      let env = Autodetection.run_auto_detection config in
      if !partial_config then
        let detected_provers = Autodetection.generate_detected_config env in
        Whyconf.set_detected_provers config detected_provers
      else begin
        let config = Whyconf.set_detected_provers config [] in
        Autodetection.generate_builtin_config env config
      end
    else config
  in
  let config =
    if !autoplugins then
      (** To remove after 13/06/21, two years after introduction of partial config *)
      set_main config (set_plugins (get_main config) [])
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
    eprintf "Error: %a@." Exn_printer.exn_printer e;
    exit 1
