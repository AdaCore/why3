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

open Why3
open Whyconf

let conf_file = ref None

let exec_name = Filename.basename Sys.argv.(0)

let option_C =
  let open Getopt in
  Key ('C', "config"), Hnd1 (AString, fun s -> conf_file := Some s),
  "<file> config file to create"

let load_config () =
  Autodetection.is_config_command := true;
  try
    Whyconf.read_config !conf_file
  with
  | Rc.CannotOpen (f, s) | Whyconf.ConfigFailure (f, s) ->
      Format.eprintf "warning: cannot read config file %s:@\n  %s@." f s;
      Whyconf.default_config f

type cmd = {
    cmd_spec : Getopt.opt list;
    cmd_desc : string;
    cmd_args : string;
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
    save_config config

  let cmd = {
      cmd_spec = [option_C];
      cmd_desc = "detect installed provers";
      cmd_args = "";
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
          Printf.eprintf "%s config add-prover: expected 2 or 3 arguments: <name> <path> [<shortcut>]\n%!"
            exec_name;
          exit 1 in
    let config = load_config () in
    let datas = read_auto_detection_data config in
    let binaries = request_manual_binaries_version datas [prover] in
    let m = compute_builtin_prover binaries datas in
    if Mprover.is_empty m then exit 1;
    let config = Manual_binary.add config prover in
    let config = update_binaries_detected binaries config in
    Format.printf "Save config to %s@." (Whyconf.get_conf_file config);
    save_config config

  let cmd = {
      cmd_spec = [option_C];
      cmd_desc = "add prover";
      cmd_args = " <name> <path> [<shortcut>]";
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
      cmd_spec = [];
      cmd_desc = "list all the supported provers";
      cmd_args = "";
      cmd_name = "list-supported-provers";
      cmd_run = run;
      cmd_anon_fun = None;
    }

end

module ShowConfig = struct

  let run () =
    let config = Whyconf.init_config !conf_file in
    let rc = Whyconf.rc_of_config config in
    Rc.to_channel stdout rc

  let cmd = {
      cmd_spec = [option_C];
      cmd_desc = "show the full configution";
      cmd_args = "";
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

let do_usage () =
  Format.printf
    "@[Usage: %s config [options] <command> [options]@\n\
     Execute the given subcommand.@\n\
     @\n%t@]@?"
    exec_name
    print_commands;
  exit 0

let option_list =
  let open Getopt in
  [ Key ('C', "config"), Hnd1 (AString, fun s -> conf_file := Some s),
    "<file> config file to create";
    Key ('h', "help"), Hnd0 do_usage,
    " display this help and exit" ]

let anon_file x = raise (Getopt.GetoptFailure (Printf.sprintf "unexpected argument: %s" x))

let () =
  let i = Getopt.parse_many option_list Sys.argv !Whyconf.Args.first_arg in
  if i = Array.length Sys.argv then do_usage ();
  let cmd_name = Sys.argv.(i) in
  let cmd =
    match List.find (fun e -> e.cmd_name = cmd_name) cmds with
    | cmd -> cmd
    | exception Not_found ->
        Format.eprintf "'%s' is not a why3config command.@\n@\n%t"
          cmd_name print_commands;
        exit 1 in
  let rec cmd_usage () =
    Printf.printf "Usage: %s config %s [options]%s\n\n%s%!"
      exec_name cmd_name
      cmd.cmd_args
      (Getopt.format options);
    exit 0
  and options =
    let open Getopt in
    (Key ('h', "help"), Hnd0 cmd_usage, " display this help and exit") ::
      cmd.cmd_spec in
  let anon_fun = match cmd.cmd_anon_fun with
    | Some f -> f
    | None -> anon_file in
  Getopt.parse_all ~i:(i + 1) options anon_fun Sys.argv;
  try
    Debug.Args.set_flags_selected ();
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    Format.eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1
