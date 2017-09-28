(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

let exec_name = Filename.basename Sys.argv.(0)

let print_usage fmt () =
  let maxl = Array.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  fprintf fmt "Usage: %s <command> [options] <session directories>@\n@\n\
      Available commands:@.@[<hov>%a@]@\n@."
    exec_name
    (Pp.print_iter1 Array.iter Pp.newline
       (fun fmt e -> fprintf fmt "  %s   @[<hov>%s@]"
         (Strings.pad_right ' ' e.cmd_name maxl) e.cmd_desc)) cmds;
  let usage = Arg.usage_string
    (Arg.align Why3session_lib.common_options) "Common options:" in
  fprintf fmt "%s@\nSpecific command options: %s <command> --help@."
    usage exec_name

let () =
  if Array.length Sys.argv < 2 then begin
    print_usage err_formatter ();
    exit 1
  end;
  let cmd_name = Sys.argv.(1) in
  begin
    match cmd_name with
      | "-h" | "-help" | "--help" ->
        print_usage std_formatter (); exit 0
      | _ -> ()
  end;
  let module M = struct exception Found of cmd end in
  let cmd =
    try
      Array.iter (fun e ->
        if e.cmd_name = cmd_name
        then raise (M.Found e)) cmds;
      eprintf "command %s unknown@." cmd_name;
      print_usage err_formatter ();
      exit 1
    with M.Found cmd -> cmd
  in
  incr Arg.current;
  let cmd_usage = sprintf "Usage: %s %s [options]" exec_name cmd_name in
  Arg.parse (Arg.align cmd.cmd_spec) anon_fun cmd_usage;
  try
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1
