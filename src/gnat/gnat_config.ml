open Why3

type proof_mode =
    Then_Split
  | No_WP
  | All_Split
  | Path_WP
  | No_Split

type limit_mode =
  | Limit_Check of Gnat_expl.check
  | Limit_Line of Gnat_loc.loc

let gnatprove_why3conf_file = "why3.conf"

let default_timeout = 1

let opt_timeout : int option ref = ref None
let opt_steps : int option ref = ref None
let opt_debug = ref false
let opt_force = ref false
let opt_proof_mode = ref Then_Split
let opt_filename : string option ref = ref None
let opt_parallel = ref 1
let opt_prover : string option ref = ref None
let opt_proof_dir : string option ref = ref None

let opt_limit_line : limit_mode option ref = ref None
let opt_limit_subp : string option ref = ref None
let opt_socket_name : string ref = ref ""
let opt_standalone = ref false

let opt_prepare_shared = ref false

let set_filename s =
   if !opt_filename = None then
      opt_filename := Some s
   else
      Gnat_util.abort_with_message "Only one file name should be given."

let set_proof_mode s =
   if s = "no_wp" then
      opt_proof_mode := No_WP
   else if s = "all_split" then
      opt_proof_mode := All_Split
   else if s = "path_wp" then
      opt_proof_mode := Path_WP
   else if s = "no_split" then
      opt_proof_mode := No_Split
   else if s = "then_split" then
     opt_proof_mode := Then_Split
   else
      Gnat_util.abort_with_message
        "argument for option --proof should be one of\
        (then_split|no_wp|all_split|path_wp|no_split)."

let set_prover s =
   opt_prover := Some s

let set_timeout t =
   opt_timeout := Some t

let set_steps t =
   opt_steps := Some t

let set_socket_name s =
  opt_socket_name := s

let parse_line_spec caller s =
   try
     let args = Str.split (Str.regexp_string ":") s in
     let fn = List.hd args in
     let line = int_of_string (List.nth args 1) in
     match List.length args with
     | 2 -> Limit_Line (Gnat_loc.mk_loc_line fn line)
     | 4 ->
         let col = int_of_string (List.nth args 2) in
         let check = Gnat_expl.reason_from_string (List.nth args 3) in
         let loc = Gnat_loc.mk_loc fn line col None in
         Limit_Check (Gnat_expl.mk_check check 0 loc)
     | _ -> raise (Failure "bad arity")
   with
   | Failure "nth" ->
      Gnat_util.abort_with_message
      (caller ^ ": incorrect line specification - missing ':'")
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message
      (caller ^
        ": incorrect line specification - line or column field isn't a number")
   | Failure "bad arity" ->
      Gnat_util.abort_with_message
      (caller ^
        ": incorrect line specification - invalid parameter number, must be \
         2 or 4")

let set_proof_dir s = opt_proof_dir := Some  s

let set_limit_line s = opt_limit_line := Some (parse_line_spec "limit-line" s)
let set_limit_subp s = opt_limit_subp := Some s

let usage_msg =
  "Usage: gnatwhy3 [options] file"

let options = Arg.align [
   "-t", Arg.Int set_timeout,
          " Set the timeout in seconds (default is 1 second)";
   "--timeout", Arg.Int set_timeout,
          " Set the timeout in seconds (default is 1 second)";
   "--steps", Arg.Int set_steps,
       " Set the steps (default: no steps). " ^
         "This option is *not* passed to alt-ergo, " ^
         "only used to compute the timeout";
   "-j", Arg.Set_int opt_parallel,
          " Set the number of parallel processes (default is 1)";
   "-f", Arg.Set opt_force,
          " Rerun VC generation and proofs, even when the result is up to date";
   "--force", Arg.Set opt_force,
          " Rerun VC generation and proofs, even when the result is up to date";
   "--proof", Arg.String set_proof_mode,
          " Set proof mode, one of \
            (then_split|no_wp|all_split|path_wp|no_split) \
          , default is then_split";
   "--limit-line", Arg.String set_limit_line,
          " Limit proof to a file and line, given \
           by \"file:line[:column:checkkind]\"";
   "--limit-subp", Arg.String set_limit_subp,
          " Limit proof to a subprogram defined by \"file:line\"";
   "--prover", Arg.String set_prover,
          " Use prover given in argument instead of Alt-Ergo";
   "--socket", Arg.String set_socket_name,
          " The name of the socket to be used";
   "--debug", Arg.Set opt_debug,
          " Enable debug mode";
   "--standalone", Arg.Set opt_standalone,
          " spawn its own VC server";
   "--proof-dir", Arg.String set_proof_dir,
          " Specify directory to save session and manual proofs files";
   "--prepare-shared", Arg.Set opt_prepare_shared,
          " Build user libraries for manual provers";
]

let () = Arg.parse options set_filename usage_msg

let prover_merge m1 m2 =
  (* merge two prover maps; if they have share a key, keep the entry of the
     first map *)
  Whyconf.Mprover.merge (fun _ v1 v2 ->
    match v1, v2 with
    | None, x -> x
    | (Some _ as x), _ -> x)
  m1 m2

let editor_merge me1 me2 =
  Whyconf.Meditor.merge (fun _ v1 v2 ->
    match v1, v2 with
    | None, x -> x
    | (Some _ as x), _ -> x)
  me1 me2

let config =
   (* if a prover was given, read default config file and local config file *)
   try
     let gnatprove_config =
       if !opt_prepare_shared then Whyconf.read_config None
       else Whyconf.read_config (Some gnatprove_why3conf_file) in
      if !opt_prover = None then gnatprove_config
      else begin
         let conf = Whyconf.read_config None in
         let provers =
           prover_merge
             (Whyconf.get_provers gnatprove_config)
             (Whyconf.get_provers conf) in
         let editors = editor_merge (Whyconf.get_editors gnatprove_config)
                                    (Whyconf.get_editors conf) in
         Whyconf.set_editors (Whyconf.set_provers gnatprove_config provers)
                             editors
      end
   with Rc.CannotOpen _ ->
      Gnat_util.abort_with_message "Cannot read file why3.conf."

let provers : Whyconf.config_prover Whyconf.Mprover.t =
   Whyconf.get_provers config

let prover : Whyconf.config_prover =
  try
     match !opt_prover with
     | Some s ->
              Whyconf.filter_one_prover config
                (Whyconf.mk_filter_prover s)
     | None ->
           let conf =
              { Whyconf.prover_name = "Alt-Ergo for GNATprove";
                 prover_version      = "0.95";
                 prover_altern       = "";
              } in
           Whyconf.Mprover.find conf provers
  with
  | Not_found ->
        Gnat_util.abort_with_message
          "Default prover not installed or not configured."
  | Whyconf.ProverNotFound _ ->
        Gnat_util.abort_with_message
          "Selected prover not installed or not configured."
  | Whyconf.ProverAmbiguity _ ->
        Gnat_util.abort_with_message
          "Several provers match the selection."

let config_main = Whyconf.get_main (config)

let env =
   (* load plugins; may be needed for external provers *)
   if !opt_prover <> None then
     Whyconf.load_plugins config_main;
   Env.create_env (match !opt_proof_dir with
                   | Some dir -> (Filename.concat dir "_theories")
                                 :: Whyconf.loadpath config_main
                   | None -> Whyconf.loadpath config_main)

(* The function replaces %{f,t,T,m,l,d} to their corresponding values
   in the string cmd.
   This function is based on the Call_provers.actualcommand, for
   some reason not in the Why3 API nor really convenient *)
let actual_cmd ?main filename cmd =
  let m = match main with
    | None -> Whyconf.get_main config
    | Some m -> m in
  let replace_func s =
    match (Str.matched_string s).[1] with
    | '%' -> "%"
    | 'f' -> Sys.getcwd () ^ Filename.dir_sep ^ filename
    (* Can %t and %T be on an editor command line and have a meaning?
       Is it allowed by Why3config? *)
    | 't' -> string_of_int (Whyconf.timelimit m)
    | 'T' -> string_of_int (succ (Whyconf.timelimit m))
    | 'm' -> string_of_int (Whyconf.memlimit m)
    | 'l' -> Whyconf.libdir m
    | 'd' -> Whyconf.datadir m
    | 'o' -> Whyconf.libobjdir m
    | a ->  Char.escaped a in
  Str.global_substitute (Str.regexp "%.") replace_func cmd

(* function to build manual elements *)
(* pass proof dir and prover as args *)

let list_and_filter dir =
  try
    Array.fold_left (fun l f ->
                     if not (Sys.is_directory (Filename.concat dir f)) then
                       f :: l
                     else l) [] (Sys.readdir dir)
  with
  | Sys_error _ -> []

let build_shared proof_dir prover =
  let prover_name = prover.Whyconf.prover.Whyconf.prover_name in
  let shared_dir = Filename.concat proof_dir prover_name in
  let vc_files = list_and_filter shared_dir in
  let (unused, child_out) = Unix.pipe () in
  (* No better idea to get rid of child output,
     and I certainly don't want to parse it
   *)
  let user_dir = "user" in
  let prover_dir = Filename.concat user_dir prover_name in
  let update filenames =
    List.fold_left
      (fun need_update e ->
       let odir_file = Filename.concat prover_dir e in
       if not (Sys.file_exists odir_file) then
         (
           let orig_file = Filename.concat shared_dir e in
           Unix.link orig_file odir_file;
           true
         )
       else
         need_update
      ) false filenames
  in

  let exec_cmd cmd =
    let hackish_filename =
      List.fold_left (fun s fn -> s ^ " " ^ fn)
                     (List.hd vc_files) (List.tl vc_files) in
    let cmd = actual_cmd hackish_filename cmd in
    let cmd_splitted = Cmdline.cmdline_split cmd in
    let pid = Unix.fork () in
    if pid = 0 then
      (
        Unix.dup2 child_out Unix.stdout;
        Unix.dup2 child_out Unix.stderr;
        Unix.close unused;
        Unix.close child_out;
        let () = Unix.execvp (List.hd cmd_splitted)
                             (Array.of_list cmd_splitted) in
        Unix.WEXITED (1)
      )
    else
      (
        let (_, status) = Unix.waitpid [] pid in
        status
      )
  in

  let check_success res msg =
    match res with
    | Unix.WEXITED 0 -> ()
    | _ -> let () = Gnat_util.abort_with_message msg in ()
  in

  if vc_files <> [] then
  (
    if not (Sys.file_exists user_dir) then
      Unix.mkdir user_dir 0o755;
    if not (Sys.file_exists prover_dir) then
      Unix.mkdir prover_dir 0o755;
    let file_update = update vc_files in
    let old_dir = Sys.getcwd () in
    Sys.chdir prover_dir;
    if file_update && prover.Whyconf.configure_build <> "" then
      check_success (exec_cmd prover.Whyconf.configure_build)
        "Problem during build configuration for prover shared files";
    List.iter (fun cmd ->
               if cmd <> "" then
                 check_success (exec_cmd cmd)
                               "Problem during build of prover shared files")
              prover.Whyconf.build_commands;
    Sys.chdir old_dir;
    Unix.close unused;
    Unix.close child_out
  )

let filename =
   let is_not_why_loc s =
      not (Filename.check_suffix s "why" ||
           Filename.check_suffix s "mlw") in
   match !opt_filename with
   | None -> (match !opt_prepare_shared, !opt_proof_dir with
             | (true, Some pdir) -> build_shared pdir prover;
                                    let () = exit 0 in ""
             | _ -> Gnat_util.abort_with_message "No file given.")
   | Some s ->
         if is_not_why_loc s then
            Gnat_util.abort_with_message
              (Printf.sprintf "Not a Why input file: %s." s);
         s

(* loading the driver driver *)
let prover_driver : Driver.driver =
  try
    Driver.load_driver env prover.Whyconf.driver
      prover.Whyconf.extra_drivers
  with e ->
    Format.eprintf "Failed to load driver for prover: %a"
       Exn_printer.exn_printer e;
    Gnat_util.abort_with_message ""

let prover_editor () =
  Whyconf.editor_by_id config prover.Whyconf.editor

(* freeze values *)

let timeout =
   match !opt_timeout with
   | Some x -> x
   | None ->
         if !opt_steps <> None then 0
         else default_timeout

let proof_mode = !opt_proof_mode
let debug = !opt_debug
let force = !opt_force
let limit_line = !opt_limit_line

let limit_subp =
   match !opt_limit_subp with
   | None -> None
   | Some s -> Some (Ident.create_label ("GP_Subp:" ^ s))

let parallel = !opt_parallel

let unit_name =
  let suffix = ".mlw" in
  if Strings.ends_with filename suffix then
    String.sub filename 0 (String.length filename - String.length suffix)
  else Filename.chop_extension filename

let socket_name = !opt_socket_name

let stand_alone = !opt_standalone

let proof_dir = !opt_proof_dir

(* when not doing proof, stop after typing to avoid cost of the WP *)
let () =
  if proof_mode = No_WP then Debug.set_flag Typing.debug_type_only;
  Debug.set_flag (Debug.lookup_flag "fast_wp");
  let curdir = Sys.getcwd () in
  Unix.putenv "TEMP" curdir;
  Unix.putenv "TEMPDIR" curdir
