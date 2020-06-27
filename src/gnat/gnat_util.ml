open Why3
open Why3.Json_base

let abort_with_message ~internal s =
  Format.printf "{%a, %a, %a}"
  (print_json_field "error" string) s
  (print_json_field "internal" bool) internal
  (print_json_field "results" (list int)) [];
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

let find_driver_file ~conf_file ?extra_conf_file fn =
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
    else match extra_conf_file with
    | Some f ->
        let dir = Filename.dirname f in
        let fn = Filename.concat dir fn in
        if Sys.file_exists fn then fn else raise Exit
    | None -> raise Exit
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
       find_driver_file ~conf_file ?extra_conf_file base_prover.Whyconf.driver}
  in
  Whyconf.set_provers config
    (Whyconf.Mprover.map transform_driver (Whyconf.get_provers config))

let build_env_from_config ~load_plugins ~proof_dir config =
  let config_main = Whyconf.get_main config in
  ( if load_plugins then
      Whyconf.load_plugins config_main
    else (* At least load the gnat_json plugin *)
      let dirs = Whyconf.[pluginsdir (get_main config)] in
      Plugin.load ~dirs "gnat_json" );
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
  let debug_no_auto_model =
    Debug.register_flag ~desc:"When set, model labels are not added during parsing"
      "no_auto_model" in
  Debug.set_flag debug_no_auto_model;
  (* Set the vc_sp (fast_wp) everywhere. *)
  let debug_sp = Debug.register_flag "vc_sp"
    ~desc:"Use@ 'Efficient@ Weakest@ Preconditions'@ for@ verification." in
  Debug.set_flag debug_sp;
  let debug_useless_at = Debug.register_flag "ignore_useless_at"
    ~desc:"Remove@ warning@ for@ useless@ at/old." in
  Debug.set_flag debug_useless_at;
  Debug.set_flag Dterm.debug_ignore_unused_var
