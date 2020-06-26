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

type action = RenameFile of string * string

let actions = ref ([] : action list)

let spec_update =
  let open Getopt in
  [ KLong "rename-file", Hnd1 (APair (':', AString, AString),
      fun (src, dst) -> actions := RenameFile (src, dst) :: !actions),
    "<old>:<new> rename file" ]

let do_action ~env ~session action =
  ignore(env);
  match action with
  | RenameFile(src,dst) ->
     let src,dst = Session_itp.rename_file session src dst in
     let dir = Session_itp.get_dir session in
     let src = Sysutil.system_dependent_absolute_path dir src in
     let dst = Sysutil.system_dependent_absolute_path dir dst in
     assert (Sys.file_exists src);
     assert (not (Sys.is_directory src));
     assert (not (Sys.file_exists dst));
     Sys.rename src dst

let run_update () =
  let _,_,env = Whyconf.Args.complete_initialization () in
  iter_files
    (fun fname ->
     let session = read_session fname in
     List.iter (do_action ~env ~session) !actions;
     Session_itp.save_session session)

let cmd_update =
  { cmd_spec = spec_update;
    cmd_desc = "update session from the command line";
    cmd_name = "update";
    cmd_run  = run_update;
  }
