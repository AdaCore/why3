open Why3
open Wstdlib

type proof_mode =
    Progressive
  | No_WP
  | All_Split
  | Per_Path
  | Per_Check

type limit_mode =
  | Limit_Check of Gnat_expl.check
  | Limit_Line of Gnat_loc.loc

let spark_prefix =
  (Filename.dirname
          (Filename.dirname (Filename.dirname
          (Filename.dirname Sys.executable_name))))

let rec file_concat l =
  match l with
  | [] -> ""
  | [x] -> x
  | [x;y] -> Filename.concat x y
  | x :: xs -> Filename.concat x (file_concat xs)

let builtin_provers = ["altergo"; "cvc4"; "z3"]

let spark_loadpath =
  [ file_concat [spark_prefix; "share"; "why3"; "theories"];
    file_concat [spark_prefix; "share"; "why3"; "modules"];
    file_concat [spark_prefix; "share"; "spark"; "theories"]
  ]

let is_builtin_prover =
  let builtin_provers_set =
    List.fold_left (fun acc x -> Sstr.add x acc) Sstr.empty builtin_provers in
  (fun s ->
    let s = String.lowercase_ascii s in
    Sstr.mem s builtin_provers_set)

let opt_timeout : int option ref = ref None
let opt_memlimit : int option ref = ref None
let opt_ce_timeout : int option ref = ref None
let opt_warn_timeout : int ref = ref 1
let opt_steps : int option ref = ref None
let opt_debug = ref false
let opt_debug_save_vcs = ref false
let opt_force = ref false
let opt_proof_mode = ref Progressive
let opt_lazy = ref true
let opt_filename : string option ref = ref None
let opt_parallel = ref 1
let opt_prover : string option ref = ref None
let opt_proof_dir : string option ref = ref None
let opt_ce_mode = ref false
let opt_ce_prover = ref "cvc4_ce"
let opt_warn_prover = ref None

let opt_limit_line : limit_mode option ref = ref None
let opt_limit_region : Gnat_loc.region option ref = ref None
let opt_limit_subp : string option ref = ref None
let opt_socket_name : string ref = ref ""
let opt_standalone = ref false
let opt_replay = ref false

let opt_prepare_shared = ref false

let opt_why3_conf_file : string option ref = ref None

(* Always set the debug flag that prevents from adding "model" labels everywhere
   during parsing. In SPARK, these labels are inserted during transformations
   from Ada code.
*)
let debug_no_auto_model =
  Debug.register_flag ~desc:"When set, model labels are not added during parsing"
    "no_auto_model"

let () = Debug.set_flag debug_no_auto_model

(* Set the vc_sp (fast_wp) everywhere.
TODO we may want to do something more clever in the future. *)
let debug_sp = Debug.register_flag "vc_sp"
  ~desc:"Use@ 'Efficient@ Weakest@ Preconditions'@ for@ verification."
let () = Debug.set_flag debug_sp

(* TODO we may want to revert this at some point *)
let debug_useless_at = Debug.register_flag "ignore_useless_at"
  ~desc:"Remove@ warning@ for@ useless@ at/old."
let () = Debug.set_flag debug_useless_at


(* Disable warnings for unused variables *)
let () = Debug.set_flag Dterm.debug_ignore_unused_var

let set_why3_conf s =
  if s != "" then
    opt_why3_conf_file := Some s

let set_ce_mode s =
  if s = "on" then opt_ce_mode := true
  else if s = "off" then opt_ce_mode := false
  else
    Gnat_util.abort_with_message ~internal:true
        "argument for option --counterexample should be one of\
        (on|off)."

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
   else if s = "per_path" then
      opt_proof_mode := Per_Path
   else if s = "per_check" then
      opt_proof_mode := Per_Check
   else if s = "progressive" then
     opt_proof_mode := Progressive
   else
      Gnat_util.abort_with_message ~internal:true
        "argument for option --proof should be one of\
        (per_check|per_path|progressive|no_wp|all_split)."

let set_prover s =
   opt_prover := Some s

let set_timeout t =
   opt_timeout := Some t

let set_memlimit t =
   opt_memlimit := Some t

let set_ce_timeout t =
   opt_ce_timeout := Some t

let set_warn_timeout t =
   opt_warn_timeout := t

let set_warn_prover s =
   opt_warn_prover := Some s

let set_steps t =
  if t > 0 then opt_steps := Some t

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
         Limit_Check (Gnat_expl.mk_check check 0 loc false)
     | _ ->
      Gnat_util.abort_with_message ~internal:true
      (
        "limit-line: incorrect line specification -\
         invalid parameter number, must be \
         2 or 4")
  with
   | e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message ~internal:true
      ("limit-line: incorrect line specification -\
        line or column field isn't a number")

let parse_region_spec s =
   try
     let args = Str.split (Str.regexp_string ":") s in
     match args with
     | [] ->
        Gnat_util.abort_with_message ~internal:true
        ("limit-region: incorrect region specification - missing ':'")
     | [fn;l_start;l_end] ->
         let l_start = int_of_string l_start in
         let l_end = int_of_string l_end in
         Gnat_loc.mk_region fn l_start l_end
     | _ ->
      Gnat_util.abort_with_message ~internal:true
      (
        "limit-region: incorrect line specification -\
         invalid parameter number, must be \
         3")
  with
   | e when Debug.test_flag Debug.stack_trace -> raise e
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message ~internal:true
      ("limit-region: incorrect line specification -\
        first or last line field isn't a number")

let set_proof_dir s = opt_proof_dir := Some  s

let set_limit_line s = opt_limit_line := Some (parse_line_spec s)
let set_limit_region s = opt_limit_region := Some (parse_region_spec s)
let set_limit_subp s = opt_limit_subp := Some s

let usage_msg =
  "Usage: gnatwhy3 [options] file"

let print_version_info () =
  Format.printf "Why3 for gnatprove version %s@." Config.version;
  exit 0

let show_config () =
  Format.printf "enable_ide: %s@." Config.enable_ide;
  Format.printf "enable_zarith: %s@." Config.enable_zarith;
  Format.printf "enable_zip: %s@." Config.enable_zip;
  Format.printf "enable_coq_libs: %s@." Config.enable_coq_libs;
  Format.printf "enable_coq_fp_libs: %s@." Config.enable_coq_fp_libs;
  Format.printf "enable_pvs_libs: %s@." Config.enable_pvs_libs;
  Format.printf "enable_isabelle_libs: %s@." Config.enable_isabelle_libs;
  Format.printf "enable_hypothesis_selection: %s@."
    Config.enable_hypothesis_selection;
  Format.printf "enable_local: %s@." Config.enable_local;
  Format.printf "enable_relocation: %s@." Config.enable_relocation;
  exit 0

let debug_gnat_server () =
  let debug_server =
    Debug.register_flag ~desc:"Debug gnat_server" "gnat_server"
  in
  Debug.set_flag debug_server

let options = Arg.align [
   "--version", Arg.Unit print_version_info,
          " Print version information and exit";
   "--show-config", Arg.Unit show_config,
          " Print configuration information and exit";
   "-t", Arg.Int set_timeout,
          " Set the timeout in seconds";
   "--timeout", Arg.Int set_timeout,
          " Set the timeout in seconds";
   "--memlimit", Arg.Int set_memlimit,
          " Set the memory limit in megabytes";
   "--ce-timeout", Arg.Int set_ce_timeout,
          " Set the timeout for counter examples in seconds";
   "--warn-timeout", Arg.Int set_warn_timeout,
          " Set the timeout for warnings in seconds (default is 1 second)";
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
   "--prove-all", Arg.Clear opt_lazy,
          "run prover on all VCs, do not stop on first unproved one";
   "--limit-line", Arg.String set_limit_line,
          " Limit proof to a file and line, given \
           by \"file:line[:column:checkkind]\"";
   "--limit-region", Arg.String set_limit_region,
          " Limit proof to a file and range of lines, given \
           by \"file:first_line:last_line\"";
   "--limit-subp", Arg.String set_limit_subp,
          " Limit proof to a subprogram defined by \"file:line\"";
   "--prover", Arg.String set_prover,
          " Use prover given in argument instead of Alt-Ergo";
   "--replay", Arg.Set opt_replay,
          " Do not try new proofs, only replay existing proofs";
   "--socket", Arg.String set_socket_name,
          " The name of the socket to be used";
   "--debug", Arg.Tuple [Arg.Set opt_debug; Arg.Set opt_standalone],
          " Enable debug mode; also deactivates why3server";
   "--debug-why3", Arg.String (fun s -> let debug = Debug.register_flag s ~desc:"" in
                                (* Record backtrace is done in a part of Why3
                                   that is not executed by gnatwhy3: we have to
                                   do it here. *)
                                if s = "stack_trace" then
                                  Printexc.record_backtrace true;
                                Debug.set_flag debug),
          " Enable a debug flag from Why3";
   "--debug-server", Arg.Set opt_debug,
          " Enable debug mode and keep why3server activated";
   "--debug-gnat-server", Arg.Unit debug_gnat_server,
          " Enable debug mode for gnat_server";
   "--debug-stack-trace", Arg.Tuple [Arg.Set opt_debug;
            Arg.Unit (fun () -> Debug.set_flag Debug.stack_trace;
                                Printexc.record_backtrace true)],
          " Enable debug mode; and gives stack_trace on any exception raised";
   "--debug-save-vcs", Arg.Set opt_debug_save_vcs,
          " Save VCs files when running provers";
   "--standalone", Arg.Set opt_standalone,
          " spawn its own VC server";
   "--proof-dir", Arg.String set_proof_dir,
          " Specify directory to save session and manual proofs files";
   "--prepare-shared", Arg.Set opt_prepare_shared,
          " Build user libraries for manual provers";
   "--why3-conf", Arg.String set_why3_conf,
          " Specify additionnal configuration file";
   "--counterexample", Arg.String set_ce_mode,
          " on if the counterexample for unproved VC should be get, off elsewhere";
   "--ce-prover", Arg.Set_string opt_ce_prover,
          " Give a specific prover for counterexamples";
   "--warn-prover", Arg.String set_warn_prover,
          " Give a specific prover for warnings"
]

let () = Arg.parse options set_filename usage_msg

let gnatprove_why3conf_file () = "why3.conf"

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

let find_driver_file ~conf_file fn =
  (* Here we search for the driver file. The argument [fn] is the driver path
     as returned by the Why3 API. It simply returns the path as is in the
     configuration file. We first check if the path as is points to a file.
     Then we try to find the file relative to the why3.conf file. If that also
     fails, we look into the SPARK drivers dir.
     If everything fails, we return an error message stating that we cannot find
     the driver: it also returns the configuration file [conf_file] used. *)
  (* In Why3, driver names are stored in the configuration file(s) without the
     suffix, so we add it here; for robustness we still check if it's already
     there. *)
  let fn = if Strings.ends_with fn ".drv" then fn else fn ^ ".drv" in
  try
    if Sys.file_exists fn then fn
    else match !opt_why3_conf_file with
    | Some f ->
        let dir = Filename.dirname f in
        let fn = Filename.concat dir fn in
        if Sys.file_exists fn then fn else raise Exit
    | None -> raise Exit
  with Exit ->
      let driver_file = Filename.basename fn in
      let full_path =
        file_concat [spark_prefix;"share";"why3";"drivers";driver_file] in
      if Sys.file_exists full_path then full_path
      else
        Gnat_util.abort_with_message ~internal:false
          (Format.sprintf "Could not find driver file %s referenced from %s. \
                           If this is a user-generated file, consider removing \
                           it. If not, please report." fn conf_file)

let computer_prover_str_list () =
  (* this is a string list of the requested provers by the user *)
  let prover_str_list =
    match !opt_prover with
    | None -> []
    | Some s ->
        Strings.split ',' s in
  (* sanitize list to rewrite alt-ergo into altergo *)
  let prover_str_list =
    List.map (fun s -> if s = "alt-ergo" then "altergo" else s) prover_str_list
  in
  (* in --prepare-shared mode, we don't care about built-in provers *)
  if !opt_prepare_shared then
    List.filter (fun x -> not (is_builtin_prover x)) prover_str_list
  else prover_str_list

let compute_base_provers config str_list =
  if str_list = [] && !opt_replay then
    let base_provers =
      Whyconf.Mprover.fold (fun _ v acc -> v :: acc)
        (Whyconf.get_provers config) [] in
    base_provers, None, None
  else try
    let filter_prover prover_string =
      Whyconf.filter_one_prover config (Whyconf.mk_filter_prover prover_string) in
    let base_provers = List.map filter_prover str_list in
    (* the prover for counterexample generation *)
    let base_prover_ce =
      if !opt_ce_mode then
        Some (filter_prover !opt_ce_prover)
      else
        None in
    (* unless specified explicitly, the prover for warnings is the first of the
       base provers *)
    let base_prover_warn =
      match !opt_warn_prover with
        | Some p -> Some (filter_prover p)
        | None   -> (if base_provers = [] then None else Some (List.hd base_provers))
    in
    base_provers, base_prover_ce, base_prover_warn
  with
  | e when Debug.test_flag Debug.stack_trace -> raise e
  | Not_found ->
    Gnat_util.abort_with_message ~internal:false
      "Default prover not installed or not configured."
  | Whyconf.ProverNotFound _ ->
    Gnat_util.abort_with_message ~internal:false
      "Selected prover not installed or not configured."
  | Whyconf.ProverAmbiguity _ ->
    Gnat_util.abort_with_message ~internal:false
      "Several provers match the selection."

(* we slightly change the config so that drivers files are referenced
   with the right prefix. *)
let get_gnatprove_config config =
  let conf_file = Whyconf.get_conf_file config in
  let transform_driver (base_prover: Whyconf.config_prover) =
    {base_prover with Whyconf.driver =
       find_driver_file ~conf_file base_prover.Whyconf.driver}
  in
  Whyconf.set_provers config
    (Whyconf.Mprover.map transform_driver (Whyconf.get_provers config))

(* Depending on what kinds of provers are requested, environment loading is a
 * bit different, hence we do this all together here *)

let provers, prover_ce, prover_warn, config, env =
  let prover_str_list = computer_prover_str_list () in
  (* did the user request some prover which is not shipped with SPARK? *)
  let builtin_provers_only = List.for_all is_builtin_prover prover_str_list in
  (* now load the configuration of Why3 *)
  let config =
     (* We only read the default config file ($HOME/.why3.conf) in replay mode,
        or if the option --prover was given, with a non-builtin prover *)
     try
       let gnatprove_config =
         get_gnatprove_config (Whyconf.read_config (Some (gnatprove_why3conf_file ()))) in
       if not !opt_replay && builtin_provers_only then gnatprove_config
       else begin
           let conf = get_gnatprove_config (Whyconf.read_config !opt_why3_conf_file) in
           let provers =
             prover_merge
               (Whyconf.get_provers gnatprove_config)
               (Whyconf.get_provers conf) in
           let editors = editor_merge (Whyconf.get_editors gnatprove_config)
                                      (Whyconf.get_editors conf) in
           let shortcuts =
             shortcut_merge (Whyconf.get_prover_shortcuts gnatprove_config)
                            (Whyconf.get_prover_shortcuts conf) in
           let config =
             Whyconf.set_editors
               (Whyconf.set_provers ~shortcuts gnatprove_config provers)
               editors
           in
           config
        end
     with e when Debug.test_flag Debug.stack_trace -> raise e
     | Rc.CannotOpen (f,s) ->
       Gnat_util.abort_with_message ~internal:false
         (Format.sprintf "cannot read file %s: %s" f s)
     | Whyconf.ConfigFailure (_,s) ->
         (* no need to mention the file, it is already mentioned in the error
            message s *)
       Gnat_util.abort_with_message ~internal:false
         (Format.sprintf "%s" s)
  in

  (* now we build the Whyconf.config_prover for all requested provers
   * and for the prover for counterexample generation *)
  let base_provers, base_prover_ce, base_prover_warn =
    compute_base_provers config prover_str_list in
  let env =
    let config_main = Whyconf.get_main config in
    (* load plugins; may be needed for external provers *)
    if not builtin_provers_only then
      Whyconf.load_plugins config_main;
    let base_loadpath = spark_loadpath @ Whyconf.loadpath config_main in
    let extended_loadpath =
      match !opt_proof_dir with
      | Some dir -> (Filename.concat dir "_theories") :: base_loadpath
      | None -> base_loadpath
    in
    Env.create_env extended_loadpath  in
  let provers =
    List.map (fun x -> x.Whyconf.prover) base_provers in
  let prover_ce =
    Opt.map (fun conf_prover -> conf_prover.Whyconf.prover) base_prover_ce
  in
  let prover_warn =
    Opt.map (fun conf_prover -> conf_prover.Whyconf.prover) base_prover_warn
  in
  provers, prover_ce, prover_warn, config, env

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

let build_shared proof_dir (prover: Whyconf.prover) =
  let prover_name = prover.Whyconf.prover_name in
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
      List.fold_left (fun s fn -> s ^ fn)
                     (List.hd vc_files) (List.tl vc_files) in
    let cmd = actual_cmd hackish_filename cmd in
    Sys.command cmd
  in

  let check_success res msg =
    if res <> 0 then Gnat_util.abort_with_message ~internal:true msg
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
    let config_prover = Whyconf.get_prover_config config prover in
    let configure_build = config_prover.Whyconf.configure_build in
    if file_update && configure_build <> "" then
      check_success (exec_cmd configure_build)
        "Problem during build configuration for prover shared files";
    List.iter (fun cmd ->
               if cmd <> "" then
                 check_success (exec_cmd cmd)
                               "Problem during build of prover shared files")
              config_prover.Whyconf.build_commands;
    Sys.chdir old_dir;
    Unix.close unused;
    Unix.close child_out
  )

let () =
  (* check whether we are in prepare_shared mode, if so, do just that *)
  match !opt_prepare_shared, !opt_proof_dir with
  | (true, Some pdir) ->
    List.iter (fun prover ->
      build_shared pdir prover) provers;

    let () = match prover_ce with
    | Some prover_ce ->
      build_shared pdir prover_ce;
    | None -> () in

    exit 0
  | _ -> ()

let counterexamples = !opt_ce_mode

let manual_prover =
  (* sanity check - we don't allow combining
     manual with other provers. Or said otherwise, if there is more than one
     prover, they must all be automatic. *)
  match provers with
  | [] -> None
  | [x] when
      let config_prover = Whyconf.get_prover_config config x in
      config_prover.Whyconf.interactive ->
        Some x
  | _ :: _ :: _ when
     List.exists (fun p ->
       let config_prover = Whyconf.get_prover_config config p in
       config_prover.Whyconf.interactive) provers
     && not !opt_replay
     ->
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

let limit_time ~prover ~warning =
  if warning then
    !opt_warn_timeout
  else match prover_ce, !opt_timeout with
  | Some p, _ when prover = p.Whyconf.prover_name &&
                   !opt_ce_timeout <> None ->
      Opt.get !opt_ce_timeout
  | _, None -> Call_provers.empty_limit.Call_provers.limit_time
  | _, Some x -> x

type steps_convert = { add : int; mult : int }

module Steps_conversion : sig

  val convert : prover : string -> int -> int
  val back_convert : prover : string -> int -> int

end = struct

  let convert_data =
    ["cvc4", { add = 15000; mult = 35 };
     "z3",   { add = 450000; mult = 800 }]

  let starts_with a b =
    if String.length a > String.length b then false
    else
      a = String.sub (String.lowercase_ascii b) 0 (String.length a)

  let num_convert conv c =
    conv.add + conv.mult * c

  let num_back_convert conv c =
  (* we are adding 1 to the count because the division will round downwards,
     but we want to have the property that checks are proved with the
     reported steps *)
    (max 0 (c - conv.add)) / conv.mult + 1

  let find_convert prover =
    let rec aux l =
      match l with
      | [] -> { add = 0 ; mult = 1 }
      | (name, conv) :: rest ->
          if starts_with name prover then conv
          else aux rest
    in
    aux convert_data

  let convert ~prover c =
    num_convert (find_convert prover) c

  let back_convert ~prover c =
    num_back_convert (find_convert prover) c

end


let steps ~prover =
  match manual_prover, !opt_steps with
  | Some _, _ | _, None -> Call_provers.empty_limit.Call_provers.limit_steps
  | _, Some c -> Steps_conversion.convert ~prover c

let limit_mem () =
  match manual_prover, !opt_memlimit with
  | Some _, _ | _, None -> Call_provers.empty_limit.Call_provers.limit_mem
  | _, Some m -> m

let back_convert_steps = Steps_conversion.back_convert

let limit ~prover ~warning =
  { Call_provers.limit_mem = limit_mem ();
    Call_provers.limit_time = limit_time ~prover ~warning;
    limit_steps = steps ~prover}

let proof_mode = !opt_proof_mode
let lazy_ = !opt_lazy
let debug = !opt_debug
let debug_save_vcs = !opt_debug_save_vcs

let debug_keep_vcs = Debug.register_info_flag "keep_vcs" ~desc:"Keep@ intermediate@ prover@ files."

let _ =
  if debug_save_vcs || debug then
    Debug.set_flag debug_keep_vcs

let force = !opt_force
let limit_line = !opt_limit_line
let limit_region = !opt_limit_region

let limit_subp =
   match !opt_limit_subp with
   | None -> None
   | Some s -> Some (Ident.create_attribute ("GP_Subp:" ^ s))

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
(*  Debug.set_flag (Debug.lookup_flag "fast_wp");*)
  let curdir = Sys.getcwd () in
  Unix.putenv "TEMP" curdir;
  Unix.putenv "TEMPDIR" curdir

let is_selected_prover p =
  try
    Some (List.find (fun g ->
      g = p) provers)
  with Not_found -> None

let is_ce_prover s p =
  counterexamples &&
  match prover_ce with
  | None -> false
  | Some cep ->
      let prover = (Session_itp.get_proof_attempt_node s p).Session_itp.prover in
      cep = prover

let replay = !opt_replay
