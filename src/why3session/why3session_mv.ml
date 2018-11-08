
open Why3
open Why3session_lib
open Session_itp

let from_file = ref ""
let to_file = ref ""

let spec_mv =
  ("-i", Arg.String (fun s -> from_file := s),
       "<file> file to move") ::
  ("-o", Arg.String (fun s -> to_file := s),
       "<file> path to move to") ::
  common_options

let move ~env ~session from_file to_file =
  let dir = Filename.dirname session in
  let from_file = Sysutil.relativize_filename dir (Sysutil.cannonical from_file) in
  let to_file = Sysutil.relativize_filename dir (Sysutil.cannonical to_file) in
  (* TODO match exceptions ? *)
  let session, shape_version = load_session dir in
  let (_: session) = move_file ~shape_version ~check_reload:true env session from_file to_file in
  ()

let run_mv () =
  let env,_config,should_exit1 = read_env_spec () in
  if should_exit1 || !from_file = "" || !to_file = "" then exit 1;
  iter_files (fun session -> move ~env ~session !from_file !to_file)

let cmd_mv =
  { cmd_spec = spec_mv;
    cmd_desc = "change an .mlw file in the session to another .mlw file";
    cmd_name = "mv";
    cmd_run  = run_mv;
  }
