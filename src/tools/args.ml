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

let common_options = [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> Read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  Debug.Args.desc_debug_list;
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug ]

let initialize options default usage =
  Arg.parse (Arg.align (List.append options common_options)) default usage;
  let config = Whyconf.read_config !opt_config in
  let config = List.fold_left Whyconf.merge_config config !opt_extra in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  Debug.Args.set_flags_selected ();
  let lp = List.rev_append !opt_loadpath (Whyconf.loadpath main) in
  (Env.create_env lp, config)
