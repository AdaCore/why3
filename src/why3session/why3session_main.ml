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
open Why3session_lib

module Main () = struct

let cmds =
  [
    Why3session_create.cmd;
    Why3session_info.cmd;
    Why3session_html.cmd;
    Why3session_latex.cmd;
    Why3session_update.cmd_update;
    Why3session_output.cmd;
    (* Why3session_csv.cmd; Why3session_copy.cmd_mod; Why3session_copy.cmd_copy;
       Why3session_copy.cmd_archive; Why3session_rm.cmd;
       Why3session_run.cmd; *)
  ]

let print_commands fmt =
  let maxl =
    List.fold_left (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds
  in
  Format.fprintf fmt "Available commands:@\n%a"
    (Pp.print_list_suf Pp.newline (fun fmt e ->
         Format.fprintf fmt "  %s   @[<hov>%s@]"
           (Strings.pad_right ' ' e.cmd_name maxl)
           e.cmd_desc))
    cmds

let usage_msg =
  "<command> <session> ...\n\
   Execute the given subcommand on the given sessions.\n"
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
      Format.eprintf "'%s' is not a why3session command.@\n@\n%t" cmd_name
        print_commands;
      exit 1
  in
  Whyconf.Args.add_command cmd_name;
  let usage_msg = cmd.cmd_usage in
  let options = Whyconf.Args.all_options cmd.cmd_spec usage_msg "" in
  Getopt.parse_all ~i:(i + 1) options add_session_file Sys.argv;
  begin
    if no_session_file () then
      let extra_help =
        Format.asprintf "Please provide at least one session as argument.@\n%s" extra_help
      in
      Whyconf.Args.exit_with_usage ~extra_help usage_msg;
  end;
  try cmd.cmd_run () with
  | e when not (Debug.test_flag Debug.stack_trace) ->
    Format.eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1

end

let () = Whyconf.register_command "session" (module Main)
