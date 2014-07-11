(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

let opt_config = ref None
let opt_extra = ref []
let opt_loadpath = ref []
let opt_help = ref false

let common_options_head = [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  Debug.Args.desc_debug;
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug_list;
]

let common_options_tail = [
  "-h", Arg.Set opt_help,
      " print this list of options";
  "-help", Arg.Set opt_help,
      "";
  "--help", Arg.Set opt_help,
      " same as -h";
]

let align_options options =
  Arg.align (common_options_head @ options @ common_options_tail)

let initialize ?(extra_help=Format.pp_print_newline) options default usage =
  let options = align_options options in
  Arg.parse options default usage;

  if !opt_help then begin
    Format.printf "@[%s%a@]" (Arg.usage_string options usage) extra_help ();
    exit 0
  end;

  let config = Whyconf.read_config !opt_config in
  let config = List.fold_left Whyconf.merge_config config !opt_extra in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  Debug.Args.set_flags_selected ();
  if Debug.Args.option_list () then exit 0;

  let lp = List.rev_append !opt_loadpath (Whyconf.loadpath main) in
  (Env.create_env lp, config)

let exit_with_usage options usage =
  Arg.usage (align_options options) usage;
  exit 1
