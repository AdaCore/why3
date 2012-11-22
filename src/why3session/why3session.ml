(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Why3session_lib

let cmds =
  [|
    Why3session_info.cmd;
    Why3session_latex.cmd;
    Why3session_html.cmd;
    Why3session_csv.cmd;
    Why3session_copy.cmd_mod;
    Why3session_copy.cmd_copy;
    Why3session_copy.cmd_archive;
    Why3session_rm.cmd;
    Why3session_output.cmd;
    Why3session_run.cmd;
  |]

let exec_name = Sys.argv.(0)

let print_usage () =
  let maxl = Array.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  eprintf "%s <command> [options] <session directories>@\n@\navailable commands:@.@[<hov>%a@]@\n@."
    exec_name
    (Pp.print_iter1 Array.iter Pp.newline
       (fun fmt e -> fprintf fmt "%s   @[<hov>%s@]"
         (Strings.pad_right ' ' e.cmd_name maxl) e.cmd_desc)) cmds;
  Arg.usage (Arg.align Why3session_lib.common_options) "common options:";
  eprintf "@\nspecific command options: %s <command> -help@." exec_name;
  exit 1

let () =
  if Array.length Sys.argv < 2 then print_usage ();
  let cmd_name = Sys.argv.(1) in
  begin
    match cmd_name with
      | "-h" | "--help" -> print_usage ()
      | "-v" | "--version" -> print_version (); exit 0
      | _ -> ()
  end;
  let module M = struct exception Found of cmd end in
  let cmd =
    try
      Array.iter (fun e ->
        if e.cmd_name = cmd_name
        then raise (M.Found e)) cmds;
      eprintf "command %s unknown@." cmd_name;
      print_usage ()
    with M.Found cmd -> cmd
  in
  incr Arg.current;
  let cmd_usage = sprintf "%s %s [options]:" Sys.argv.(0) cmd_name in
  Arg.parse (Arg.align cmd.cmd_spec) anon_fun cmd_usage;
  try
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1
