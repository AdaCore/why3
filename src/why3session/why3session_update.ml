open Why3
open Why3session_lib

type action = RenameFile of string * string

let actions = ref ([] : action list)

let spec_update =
  let from_file = ref "" in
  ("-rename-file",
   Arg.(Tuple [Set_string from_file;
               String (fun s -> actions := RenameFile(!from_file,s) :: !actions)]),
       "<oldname> <newname> rename file") ::
  common_options

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
  let env,_config,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  iter_files
    (fun fname ->
     let session, _ = read_session fname in
     List.iter (do_action ~env ~session) !actions;
     Session_itp.save_session session)

let cmd_update =
  { cmd_spec = spec_update;
    cmd_desc = "update session from the command line";
    cmd_name = "update";
    cmd_run  = run_update;
  }
