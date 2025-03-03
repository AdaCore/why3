open Why3
open Why3.Json_base

let abort_with_message ~internal s =
  print_json Format.std_formatter 
    (Record [ "error", String s;
              "internal", Bool internal;
              "results", List []]);
  exit 1

let () =
  Printexc.set_uncaught_exception_handler
    (fun exn raw_backtrace ->
       let bt = Printexc.raw_backtrace_to_string raw_backtrace in
       let msg = Format.asprintf "%a\nBacktrace is the following:\n%s@."
           Why3.Exn_printer.exn_printer exn bt
       in
       let internal =
         match exn with
         | Out_of_memory -> false
         | _ -> true in
       abort_with_message ~internal msg)

let colon = ':'

let colon_split s =
   let acc : string list ref = ref [] in
   let last_index = ref (String.length s) in
   let cur_index = ref (String.length s - 1) in
   try
      while true do
         cur_index := String.rindex_from s (!cur_index - 1) colon;
         acc :=
            String.sub s (!cur_index + 1) (!last_index - !cur_index - 1):: !acc;
         last_index := !cur_index;
      done;
      !acc
   with Invalid_argument _ | Not_found ->
      String.sub s 0 (!last_index) :: !acc

let why3_prefix =
  Filename.dirname (Filename.dirname Sys.executable_name)
let spark_prefix =
  Filename.dirname (Filename.dirname why3_prefix)

let gnatprove_why3conf_file = "why3.conf"

let rec file_concat l =
  match l with
  | [] -> ""
  | [x] -> x
  | [x;y] -> Filename.concat x y
  | x :: xs -> Filename.concat x (file_concat xs)

let spark_loadpath =
  [ file_concat [why3_prefix; "share"; "why3"; "theories"];
    file_concat [why3_prefix; "share"; "why3"; "modules"];
    file_concat [spark_prefix; "share"; "spark"; "theories"]
  ]

let find_driver_file ~conf_file ?extra_conf_file (extra_dir,fn) =
  (* Here we search for the driver file. The argument [fn] is the driver path as
     returned by the Why3 API (as is in the configuration file), and [extra_dir]
     optionally contains the subdir to which [fn] is relative. We first check if
     the path as is points to a file.  Then we try to find the file relative to the
     why3.conf file. If that also fails, we look into the SPARK drivers dir.
     If everything fails, we return an error message stating that we cannot find
     the driver: it also returns the configuration file [conf_file] used. *)
  (* In Why3, driver names are stored in the configuration file(s) without the
     suffix, so we add it here; for robustness we still check if it's already
     there. *)
  let fn = if Strings.has_suffix fn ~suffix:".drv" then fn else fn ^ ".drv" in
  try
    if Sys.file_exists fn then fn
    else match extra_conf_file with
    | Some f ->
        let dir = Filename.dirname f in
        let fn = Filename.concat dir fn in
        if Sys.file_exists fn then fn else raise Exit
    | None -> raise Exit
    with Exit ->
    try begin match extra_dir with
    | Some f ->
        let dir = Filename.dirname f in
        let fn = Filename.concat dir fn in
        if Sys.file_exists fn then fn else raise Exit
    | None -> raise Exit
    end
    with Exit ->
      let driver_file = Filename.basename fn in
      let full_path =
        file_concat [why3_prefix;"share";"why3";"drivers";driver_file] in
      if Sys.file_exists full_path then full_path
      else
        abort_with_message ~internal:false
          (Format.sprintf "Could not find driver file %s referenced from %s. \
                           If this is a user-generated file, consider removing \
                           it. If not, please report." fn conf_file)


let get_gnatprove_config ?extra_conf_file config =
  let conf_file = Whyconf.get_conf_file config in
  let transform_driver (base_prover: Whyconf.config_prover) =
    {base_prover with Whyconf.driver =
       None, find_driver_file ~conf_file ?extra_conf_file base_prover.Whyconf.driver}
  in
  Whyconf.set_provers config
    (Whyconf.Mprover.map transform_driver (Whyconf.get_provers config))

let build_env_from_config ~load_plugins ~proof_dir config =
  let config_main = Whyconf.get_main config in
  ( if load_plugins then
      Whyconf.load_plugins config_main
    else (* At least load the gnatwhy3 plugins *)
      let dirs = [Whyconf.pluginsdir (Whyconf.get_main config)] in
      List.iter (Plugin.load ~dirs) ["gnat_json"; "ada_terms"] );
  let base_loadpath = spark_loadpath @ Whyconf.loadpath config_main in
  let extended_loadpath =
    match proof_dir with
    | Some dir -> (Filename.concat dir "_theories") :: base_loadpath
    | None -> base_loadpath
  in
  Env.create_env extended_loadpath

let set_debug_flags_gnatprove () =
  (* Always set the debug flag that prevents from adding "model" labels everywhere
     during parsing. In SPARK, these labels are inserted during transformations
     from Ada code.
  *)
  (* Set the vc_sp (fast_wp) everywhere. *)
  let debug_sp = Debug.register_flag "vc_sp"
    ~desc:"Use@ 'Efficient@ Weakest@ Preconditions'@ for@ verification." in
  Debug.set_flag debug_sp;
  (* Reduction_engine.warn_reduction_aborted *)
  let warn_reduction_aborted = Loc.register_warning "reduction_aborted" "" in
  (* We should use Typing.warn_useless_at and Typing.warn_unused_expression, but they are not exported*)
  let warning_useless_at = Loc.register_warning "useless_at"
    "Warning@ for@ useless@ at/old." in
  let warn_unused_expression = Loc.register_warning "unused_expression"
    "Warning@ for@ useless@ expression." in
  (* Export from Session_itp *)
  let warn_missing_shapes = Loc.register_warning "missing_shapes"
    "Warn about missing shape file or missing compression support"
  in
  Loc.disable_warning warning_useless_at;
  Loc.disable_warning warn_unused_expression;
  Loc.disable_warning warn_reduction_aborted;
  Loc.disable_warning Theory.warn_axiom_abstract;
  Loc.disable_warning warn_missing_shapes;
  Loc.disable_warning Dterm.warn_unused_variable;
  Loc.disable_warning Smtv2_model_parser.warn

