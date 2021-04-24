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

open Format
open Why3
open Whyconf

let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_attrs = ref false

let option_list =
  let open Getopt in
  Args.common_options @
  [ KLong "print-libdir", Hnd0 (fun () -> printf "%s@." Config.libdir; exit 0),
    " print location of binary components (plugins, etc)";
    KLong "print-datadir", Hnd0 (fun _ -> printf "%s@." Config.datadir; exit 0),
    " print location of non-binary data (modules, etc)";
    KLong "version",
    Hnd0 (fun _ -> printf "Why3 platform, version %s@." Config.version; exit 0),
    " print version information";
  ]

let command_path = match Config.localdir with
  | Some p -> Filename.concat p "bin"
  | None -> Filename.concat Config.libdir "commands"

let extra_help fmt commands =
  fprintf fmt "Available commands:@\n";
  List.iter (fprintf fmt "  %s@\n") commands

let tools_ext =
  if Dynlink.is_native then ".cmxs" else ".cma"

let available_commands () =
  let commands = Sys.readdir command_path in
  Array.sort String.compare commands;
  let re = Re.Str.regexp "^why3\\([^.]+\\)\\([.].*\\)" in
  let commands = Array.fold_left (fun acc v ->
    if Re.Str.string_match re v 0 then
      let w = Re.Str.matched_group 1 v in
      if Re.Str.matched_group 2 v = tools_ext then w :: acc else acc
    else acc) [] commands in
  List.rev commands

let do_usage () =
  Format.printf
    "@[Usage: %s [options] <command>@\n\
     Execute the given subcommand.@\n\
     @\n%s@\n%a@]@?"
    (Filename.basename Sys.argv.(0))
    (Getopt.format option_list)
    extra_help (available_commands ());
  exit 0

let option_list =
  let open Getopt in
  (Key ('h', "help"), Hnd0 do_usage,
   " display this help and exit") ::
  option_list

let command cur =
  let sscmd, args =
    let nargs = Array.length Sys.argv in
    let sscmd = Sys.argv.(cur) in
    let cur = cur + 1 in
    if sscmd = "help" then begin
      if cur = nargs then do_usage ();
      let sscmd = Sys.argv.(cur) in
      sscmd, ["--help"]
    end else begin
      let args = ref [] in
      for i = 1 to nargs - 1 do
        if i <> cur - 1 then args := Sys.argv.(i) :: !args;
      done;
      sscmd, List.rev !args
    end in
  let cmd =
    let scmd = "why3" ^ sscmd ^ tools_ext in
    let cmd = Filename.concat command_path scmd in
    if not (Sys.file_exists cmd) then
      begin
        eprintf "'%s' is not a Why3 command.@\n@\n%a"
          sscmd extra_help (available_commands ());
        exit 1;
      end;
      cmd in
  let args = Array.of_list args in
  let argc = Array.length args in
  let argi = Array.length Sys.argv - argc in
  Array.blit args 0 Sys.argv argi argc;
  Whyconf.Args.first_arg := argi;
  Whyconf.Args.add_command sscmd;
  try
    Dynlink.allow_unsafe_modules true;
    Dynlink_wrapper.loadfile cmd;
    exit 0
  with Dynlink.Error e ->
    Printf.eprintf "Failed to load %s: %s\n%!" cmd (Dynlink.error_message e);
    exit 1

let () =
  try
    let i = Getopt.parse_many option_list Sys.argv 1 in
    if i < Array.length Sys.argv then command i;
    ignore (Args.complete_initialization ());
    do_usage ()
  with
  | e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
