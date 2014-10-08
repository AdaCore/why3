open Why3
open Stdlib

type proof_mode =
    Then_Split
  | No_WP
  | All_Split
  | Path_WP
  | No_Split

type limit_mode =
  | Limit_Check of Gnat_expl.check
  | Limit_Line of Gnat_loc.loc

type prover =
  { driver : Driver.driver;
    prover : Whyconf.config_prover;
    editor : Whyconf.config_editor
  }

let gnatprove_why3conf_file = "why3.conf"

let is_builtin_prover =
  let builtin_provers =
    Sstr.add "altergo" (Sstr.add "cvc4" Sstr.empty) in
  (fun s ->
    let s = String.lowercase s in
    Sstr.mem s builtin_provers)

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
      Gnat_util.abort_with_message ~internal:true
      "Only one file name should be given."

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
      Gnat_util.abort_with_message ~internal:true
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

let parse_line_spec s =
   try
     let args = Str.split (Str.regexp_string ":") s in
     match args with
     | [] ->
        Gnat_util.abort_with_message ~internal:true
        ("limit-line: incorrect line specification - missing ':'")
     | [fn;line] ->
         let line = int_of_string line in
         Limit_Line (Gnat_loc.mk_loc_line fn line)
     | [fn;line;col;check] ->
         let line = int_of_string line in
         let col = int_of_string col in
         let check = Gnat_expl.reason_from_string check in
         let loc = Gnat_loc.mk_loc fn line col None in
         Limit_Check (Gnat_expl.mk_check check 0 loc)
     | _ ->
      Gnat_util.abort_with_message ~internal:true
      (
        "limit-line: incorrect line specification -\
         invalid parameter number, must be \
         2 or 4")
  with
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message ~internal:true
      ("limit-line: incorrect line specification -\
        line or column field isn't a number")

let set_proof_dir s = opt_proof_dir := Some  s

let set_limit_line s = opt_limit_line := Some (parse_line_spec s)
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

let merge_opt_keep_first _ v1 v2 =
  match v1, v2 with
  | None, x -> x
  | (Some _ as x), _ -> x

let prover_merge m1 m2 =
  Whyconf.Mprover.merge merge_opt_keep_first m1 m2

let editor_merge me1 me2 =
  Whyconf.Meditor.merge merge_opt_keep_first me1 me2

let shortcut_merge s1 s2 =
  Mstr.merge merge_opt_keep_first s1 s2

(* Depending on what kinds of provers are requested, environment loading is a
 * bit different, hence we do this all together here *)

let provers, config, env =
  (* this is a string list of the requested provers by the user *)
  let prover_str_list =
    match !opt_prover with
    | None -> []
    | Some s ->
        Strings.split ',' s in
  (* in --prepare-shared mode, we don't care about built-in provers *)
  let prover_str_list =
    if !opt_prepare_shared then
      List.filter (fun x -> not (is_builtin_prover x)) prover_str_list
    else prover_str_list in
  (* did the user request some prover which is not shipped with SPARK? *)
  let builtin_provers_only =
    prover_str_list = [] || List.for_all is_builtin_prover prover_str_list in
  (* now load the configuration of Why3 *)
  let config =
     (* We only read the default config file ($HOME/.why3.conf) if the option
      * --prover was given, with a non-builtin prover *)
     try
       let gnatprove_config =
         if !opt_prepare_shared then Whyconf.read_config None
         else Whyconf.read_config (Some gnatprove_why3conf_file) in
       if builtin_provers_only then gnatprove_config
        else begin
           let conf = Whyconf.read_config None in
           let provers =
             prover_merge
               (Whyconf.get_provers gnatprove_config)
               (Whyconf.get_provers conf) in
           let editors = editor_merge (Whyconf.get_editors gnatprove_config)
                                      (Whyconf.get_editors conf) in
           let shortcuts =
             shortcut_merge (Whyconf.get_prover_shortcuts gnatprove_config)
                            (Whyconf.get_prover_shortcuts conf) in
           Whyconf.set_editors
             (Whyconf.set_provers ~shortcuts gnatprove_config provers)
             editors
        end
     with Rc.CannotOpen _ ->
       Gnat_util.abort_with_message ~internal:true "Cannot read file why3.conf."
  in
  (* configured_provers is the map of all provers that Why3 knows about *)
  let configured_provers : Whyconf.config_prover Whyconf.Mprover.t =
     Whyconf.get_provers config in
  (* now we build the Whyconf.config_prover for all requested provers *)
  let base_provers =
    try match prover_str_list with
    | [] when !opt_prepare_shared -> []
    | [] ->
       let conf =
          { Whyconf.prover_name = "altergo";
             prover_version      = "0.95";
             prover_altern       = "";
          } in
       [ Whyconf.Mprover.find conf configured_provers ]
    | l ->
        List.map (fun s ->
          Whyconf.filter_one_prover config (Whyconf.mk_filter_prover s)) l
    with
    | Not_found ->
          Gnat_util.abort_with_message ~internal:false
            "Default prover not installed or not configured."
    | Whyconf.ProverNotFound _ ->
          Gnat_util.abort_with_message ~internal:false
            "Selected prover not installed or not configured."
    | Whyconf.ProverAmbiguity _ ->
          Gnat_util.abort_with_message ~internal:false
            "Several provers match the selection." in
  let env =
    let config_main = Whyconf.get_main (config) in
    (* load plugins; may be needed for external provers *)
    if not builtin_provers_only then
      Whyconf.load_plugins config_main;
    Env.create_env (match !opt_proof_dir with
                    | Some dir -> (Filename.concat dir "_theories")
                                  :: Whyconf.loadpath config_main
                    | None -> Whyconf.loadpath config_main) in
  (* this function loads the driver for a given prover *)
  let prover_driver base_prover =
    try
      Driver.load_driver env base_prover.Whyconf.driver
        base_prover.Whyconf.extra_drivers
    with e ->
      let s =
        Pp.sprintf "Failed to load driver for prover: %a"
             Exn_printer.exn_printer e in
      Gnat_util.abort_with_message ~internal:true s in
  (* this function loads the editor for a given prover, otherwise returns a
     default value *)
  let prover_editor prover =
    try Whyconf.editor_by_id config prover.Whyconf.editor
    with Not_found ->
      { Whyconf.editor_name = "";
        editor_command = "";
        editor_options = [] }
    in
  (* now we build the prover record for each requested prover *)
  let provers =
    List.map (fun base ->
      { driver = prover_driver base;
        prover = base;
        editor = prover_editor base }) base_provers in
  provers, config, env

(* The function replaces %{f,t,T,m,l,d} to their corresponding values
   in the string cmd.
   This function is based on the Call_provers.actualcommand, for
   some reason not in the Why3 API nor really convenient *)
(* ??? delete this and use the one from Call_provers *)

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
    | _ -> let () = Gnat_util.abort_with_message ~internal:true msg in ()
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

let () =
  (* check whether we are in prepare_shared mode, if so, do just that *)
  match !opt_prepare_shared, !opt_proof_dir with
  | (true, Some pdir) ->
      List.iter (fun prover -> build_shared pdir prover.prover) provers;
      exit 0
  | _ -> ()

let manual_prover =
  (* sanity check - we found at least one prover, and don't allow combining
     manual with other provers. Or said otherwise, if there is more than one
     prover, they must all be automatic.
     This is done after handling of --prepare-shared, because in that mode we
     may end of with no provers at all, e.g. when in fact all provers are
     automatic *)
  match provers with
  | [] ->
        Gnat_util.abort_with_message ~internal:true
        "no prover available, aborting"
  | [x] when x.prover.Whyconf.interactive -> Some x
  | _ :: _ :: _ when
     List.exists (fun p -> p.prover.Whyconf.interactive) provers ->
       Gnat_util.abort_with_message ~internal:false
        "manual provers cannot be combined with other provers"
  | _ ->
      None

let filename =
   let is_not_why_loc s =
      not (Filename.check_suffix s "why" ||
           Filename.check_suffix s "mlw") in
   match !opt_filename with
   | None -> Gnat_util.abort_with_message ~internal:true "No file given."
   | Some s ->
         if is_not_why_loc s then
            Gnat_util.abort_with_message ~internal:true
              (Printf.sprintf "Not a Why input file: %s." s);
         s

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
