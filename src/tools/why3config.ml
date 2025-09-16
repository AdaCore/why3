(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

module Main : functor () -> sig end
 = functor () -> struct

let exec_name = Filename.basename Sys.argv.(0)

let load_config () =
  Autodetection.is_config_command := true;
  try
    Whyconf.read_config !Whyconf.Args.opt_config
  with
  | Rc.CannotOpen (f, s) | Whyconf.ConfigFailure (f, s) ->
      Format.eprintf "warning: cannot read config file %s:@\n  %s@." f s;
      Whyconf.default_config f

type cmd = {
    cmd_desc : string;
    cmd_usage : string;
    cmd_name : string;
    cmd_run  : unit -> unit;
    cmd_anon_fun : (string -> unit) option;
  }

module DetectProvers = struct

  let run () =
    let open Autodetection in
    let config = load_config () in
    let data = read_auto_detection_data config in
    let provers = find_provers data in
    let provers =
      List.map (fun (path, name, version) ->
          { Partial.name; path; version; shortcut = None; manual = false }
        ) provers in
    ignore (compute_builtin_prover provers config data);
    let config = remove_auto_provers config in
    let config = update_provers provers config in
    (* let config = Whyconf.User.set_dirs ~libdir:Config.libdir ~datadir:Config.datadir config in *)
    Format.printf "Save config to %s@." (Whyconf.get_conf_file config);
    Whyconf.save_config config

  let cmd = {
      cmd_desc = "detect installed provers";
      cmd_usage = "\nDetect installed provers and register them into the configuration file.";
      cmd_name = "detect";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

module AddProver = struct

  let args = ref []

  let run () =
    let open Autodetection in
    let (name, path, shortcut) =
      match !args with
      | [shortcut; path; name] -> (name, path, Some shortcut)
      | [path; name] -> (name, path, None)
      | _ ->
          Printf.eprintf "%s config add-prover: expected 2 or 3 arguments: <name> <path> [shortcut]\n%!"
            exec_name;
          exit 1 in
    let config = load_config () in
    let data = read_auto_detection_data config in
    let version =
      match find_prover data name path with
      | Some v -> v
      | None ->
          Printf.eprintf "Executable %s does not match any prover named %s.\n%!" path name;
          exit 1 in
    let provers = [{ Partial.name; path; version; shortcut; manual = true }] in
    let m = compute_builtin_prover provers config data in
    if Whyconf.Mprover.is_empty m then exit 1;
    let config = update_provers provers config in
    Format.printf "Save config to %s@." (Whyconf.get_conf_file config);
    Whyconf.save_config config

  let cmd = {
      cmd_desc = "add prover";
      cmd_usage = "<name> <path> [shortcut]\nDetect prover <name> at <path> and register it into the configuration file.";
      cmd_name = "add-prover";
      cmd_run = run;
      cmd_anon_fun = Some (fun s -> args := s :: !args);
    }

end

module ListProvers = struct

  let run () =
    let open Whyconf in
    let config, _ = Args.complete_initialization () in
    Format.printf "@[<v>%a@]@."
      (Pp.print_iter2 Mprover.iter Pp.newline Pp.nothing print_prover Pp.nothing)
      (get_provers config)

  let cmd = {
      cmd_desc = "list all the registered provers";
      cmd_usage = "\nList all the provers registered in the configuration file.";
      cmd_name = "list-provers";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

module ListSupportedProvers = struct

  let run () =
    Format.printf "@[<v>%a@]@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Autodetection.list_binaries ()))

  let cmd = {
      cmd_desc = "list all the supported provers";
      cmd_usage = "\nList all the provers supported by provers-detection-data.conf.";
      cmd_name = "list-supported-provers";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

module ShowConfig = struct

  let run () =
    let config, _ = Whyconf.Args.complete_initialization () in
    let rc = Whyconf.rc_of_config config in
    Rc.to_channel stdout rc

  let cmd = {
      cmd_desc = "show the full configuration";
      cmd_usage = "\nShow the full configuration.";
      cmd_name = "show";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

let cmds = [
    AddProver.cmd;
    DetectProvers.cmd;
    ListProvers.cmd;
    ListSupportedProvers.cmd;
    ShowConfig.cmd;
  ]

let print_commands fmt =
  let maxl = List.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  Format.fprintf fmt "Available commands:@\n%a"
    (Pp.print_list_suf Pp.newline
       (fun fmt e -> Format.fprintf fmt "  %s   @[<hov>%s@]"
         (Strings.pad_right ' ' e.cmd_name maxl) e.cmd_desc)) cmds

let anon_file x = raise (Getopt.GetoptFailure (Printf.sprintf "unexpected argument: %s" x))

let usage_msg = "<command>\nExecute the given subcommand.\n"
let extra_help = Format.asprintf "%t" print_commands

let () =
  let options = Whyconf.Args.all_options [] usage_msg extra_help in
  let i = Getopt.parse_many options Sys.argv !Whyconf.Args.first_arg in
  if i = Array.length Sys.argv then
    Whyconf.Args.exit_with_usage ~extra_help usage_msg;
  let cmd_name = Sys.argv.(i) in
  let cmd =
    match List.find (fun e -> e.cmd_name = cmd_name) cmds with
    | cmd -> cmd
    | exception Not_found ->
        Format.eprintf "'%s' is not a why3config command.@\n@\n%t"
          cmd_name print_commands;
        exit 1 in
  Whyconf.Args.add_command cmd_name;
  let anon_fun = match cmd.cmd_anon_fun with
    | Some f -> f
    | None -> anon_file in
  let usage_msg = cmd.cmd_usage in
  let options = Whyconf.Args.all_options [] usage_msg "" in
  Getopt.parse_all ~i:(i + 1) options anon_fun Sys.argv;
  try
    Debug.Args.set_flags_selected ();
    if Debug.Args.option_list () then exit 0;
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    Format.eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1

end

let () = Whyconf.register_command "config" (module Main)
