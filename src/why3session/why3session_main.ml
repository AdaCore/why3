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
open Why3session_lib

let cmds =
  [
    Why3session_info.cmd;
    Why3session_html.cmd;
    Why3session_latex.cmd;
    Why3session_update.cmd_update;
(*
    Why3session_csv.cmd;
    Why3session_copy.cmd_mod;
    Why3session_copy.cmd_copy;
    Why3session_copy.cmd_archive;
    Why3session_rm.cmd;
    Why3session_output.cmd;
    Why3session_run.cmd;
*)
  ]

let exec_name = Filename.basename Sys.argv.(0)

let print_commands fmt =
  let maxl = List.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  Format.fprintf fmt "Available commands:@\n%a"
    (Pp.print_list_suf Pp.newline
       (fun fmt e -> Format.fprintf fmt "  %s   @[<hov>%s@]"
         (Strings.pad_right ' ' e.cmd_name maxl) e.cmd_desc)) cmds

let do_usage () =
  Format.printf
    "@[Usage: %s [options] <command> [options]@\n\
     Execute the given subcommand.@\n\
     @\n%t@]@?"
    exec_name
    print_commands;
  exit 0

let option_list =
  let open Getopt in
  [ Key ('h', "help"), Hnd0 do_usage,
    " display this help and exit" ]

let () =
  let i = Getopt.parse_many option_list Sys.argv 1 in
  if i = Array.length Sys.argv then do_usage ();
  let cmd_name = Sys.argv.(i) in
  let cmd =
    match List.find (fun e -> e.cmd_name = cmd_name) cmds with
    | cmd -> cmd
    | exception Not_found ->
        Format.eprintf "'%s' is not a why3session command.@\n@\n%t"
          cmd_name print_commands;
        exit 1 in
  let cmd_usage = Printf.sprintf "Usage: %s %s [options]" exec_name cmd_name in
  let options = Whyconf.Args.all_options cmd.cmd_spec cmd_usage "" in
  Getopt.parse_all ~i:(i + 1) options anon_fun Sys.argv;
  try
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    Format.eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1
