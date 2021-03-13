(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

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
    let datas = read_auto_detection_data config in
    let binaries = request_binaries_version config datas in
    ignore (compute_builtin_prover binaries datas);
    let config = set_binaries_detected binaries config in
    Format.printf "Save config to %s@." (Whyconf.get_conf_file config);
    Whyconf.save_config config

  let cmd = {
      cmd_desc = "detect installed provers";
      cmd_usage = "\nDetect installed provers.";
      cmd_name = "detect";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

module AddProver = struct

  let args = ref []

  let run () =
    let open Autodetection in
    let prover =
      match !args with
      | [shortcut; binary; name] ->
          { Manual_binary.same_as = name; binary; shortcut = Some shortcut }
      | [binary; name] ->
          { Manual_binary.same_as = name; binary; shortcut = None }
      | _ ->
          Printf.eprintf "%s config add-prover: expected 2 or 3 arguments: <name> <path> [shortcut]\n%!"
            exec_name;
          exit 1 in
    let config = load_config () in
    let datas = read_auto_detection_data config in
    let binaries = request_manual_binaries_version datas [prover] in
    let m = compute_builtin_prover binaries datas in
    if Whyconf.Mprover.is_empty m then exit 1;
    let config = Manual_binary.add config prover in
    let config = update_binaries_detected binaries config in
    Format.printf "Save config to %s@." (Whyconf.get_conf_file config);
    Whyconf.save_config config

  let cmd = {
      cmd_desc = "add prover";
      cmd_usage = "<name> <path> [shortcut]\nDetect prover <name> at <path> and register it.";
      cmd_name = "add-prover";
      cmd_run = run;
      cmd_anon_fun = Some (fun s -> args := s :: !args);
    }

end

module ListProvers = struct

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
      cmd_desc = "show the full configution";
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
    Whyconf.Args.exit_with_usage ~extra_help [] usage_msg;
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
