(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Whyconf

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
  let re = Re.Str.regexp "^why3\\([^.]+\\)\\([.].*\\)" in
  let commands = Array.fold_left (fun acc v ->
    if Re.Str.string_match re v 0 then
      let w = Re.Str.matched_group 1 v in
      if Re.Str.matched_group 2 v = tools_ext then w :: acc else acc
    else acc) [] commands in
  let commands = Wstdlib.Hstr.fold (fun s _ acc -> s :: acc) Whyconf.commands commands in
  List.sort String.compare ("help" :: commands)

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
  let sscmd =
    let nargs = Array.length Sys.argv in
    let sscmd = Sys.argv.(cur) in
    if sscmd <> "help" then sscmd
    else begin
      let cur = cur + 1 in
      if cur = nargs then do_usage ();
      let sscmd = Sys.argv.(cur) in
      Sys.argv.(cur) <- "--help";
      sscmd
    end in
  Whyconf.Args.first_arg := cur + 1;
  Whyconf.Args.add_command sscmd;
  let () =
    match Wstdlib.Hstr.find Whyconf.commands sscmd with
    | m -> let open (val m) () in (); exit 0
    | exception Not_found -> () in
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
  begin try
    Dynlink.allow_unsafe_modules true;
    Dynlink.loadfile cmd;
  with
  | Dynlink.Error (Dynlink.Library's_module_initializers_failed e) ->
      Printexc.raise_with_backtrace e (Printexc.get_raw_backtrace ())
  | Dynlink.Error e ->
    Printf.eprintf "Failed to load %s: %s\n%!" cmd (Dynlink.error_message e);
    exit 1
  end;
  match Wstdlib.Hstr.find Whyconf.commands sscmd with
  | m -> let open (val m) () in (); exit 0
  | exception Not_found ->
      Printf.eprintf "Command %s not found in %s\n%!" sscmd cmd;
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
