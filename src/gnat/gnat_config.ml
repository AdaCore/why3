open Why3

type report_mode = Fail | Fail_And_Proved | Statistics

type proof_mode =
    Then_Split
  | No_WP
  | All_Split
  | Path_WP
  | No_Split

type verbosity =
  | Normal
  | Quiet
  | Verbose

let gnatprove_why3conf_file = "why3.conf"

let default_timeout = 1

let opt_verbose = ref Normal
let opt_timeout : int option ref = ref None
let opt_steps : int option ref = ref None
let opt_report = ref Fail
let opt_debug = ref false
let opt_force = ref false
let opt_proof_mode = ref Then_Split
let opt_filename : string option ref = ref None
let opt_ide_progress_bar = ref false
let opt_parallel = ref 1
let opt_prover : string option ref = ref None
let opt_show_tag = ref false

let opt_limit_line : Gnat_loc.loc option ref = ref None
let opt_limit_subp : string option ref = ref None

let set_filename s =
   if !opt_filename = None then
      opt_filename := Some s
   else
      Gnat_util.abort_with_message "Only one file name should be given."

let set_report s =
   if s = "statistics" then
      opt_report := Statistics
   else if s = "all" then
      opt_report := Fail_And_Proved
   else if s <> "fail" then
      Gnat_util.abort_with_message
        "argument for option --report should be one of (fail|all|statistics)."

let set_proof_mode s =
   if s = "no_wp" then
      opt_proof_mode := No_WP
   else if s = "all_split" then
      opt_proof_mode := All_Split
   else if s = "path_wp" then
      opt_proof_mode := Path_WP
   else if s = "no_split" then
      opt_proof_mode := No_Split
   else if s <> "then_split" then
      Gnat_util.abort_with_message
        "argument for option --proof should be one of\
        (then_split|no_wp|all_split|path_wp|no_split)."

let set_prover s =
   opt_prover := Some s

let set_timeout t =
   opt_timeout := Some t

let set_steps t =
   opt_steps := Some t

let parse_line_spec caller s =
   try
      let index = String.rindex s ':' in
      let fn = String.sub s 0 index in
      let line =
         int_of_string (String.sub s (index + 1) (String.length s - index - 1))
      in
      Gnat_loc.mk_loc_line fn line
   with
   | Not_found ->
      Gnat_util.abort_with_message
      (caller ^ ": incorrect line specification - missing ':'")
   | Failure "int_of_string" ->
      Gnat_util.abort_with_message
      (caller ^
        ": incorrect line specification - does not end with line number")

let set_limit_line s = opt_limit_line := Some (parse_line_spec "limit-line" s)
let set_limit_subp s = opt_limit_subp := Some s

let usage_msg =
  "Usage: gnatwhy3 [options] file"

let options = Arg.align [
   "-v", Arg.Unit (fun () -> opt_verbose := Verbose),
         " Output extra verbose information";
   "--verbose", Arg.Unit (fun () -> opt_verbose := Verbose),
         " Output extra verbose information";
   "--quiet", Arg.Unit (fun () -> opt_verbose := Quiet),
         " Be quiet";
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
   "--report", Arg.String set_report,
          " Set report mode, one of (fail | all | statistics), default is fail";
   "--proof", Arg.String set_proof_mode,
          " Set proof mode, one of \
            (then_split|no_wp|all_split|path_wp|no_split) \
          , default is then_split";
   "--limit-line", Arg.String set_limit_line,
          " Limit proof to a file and line, given by \"file:line\"";
   "--limit-subp", Arg.String set_limit_subp,
          " Limit proof to a subprogram defined by \"file:line\"";
   "--prover", Arg.String set_prover,
          " Use prover given in argument instead of Alt-Ergo";
   "--ide-progress-bar", Arg.Set opt_ide_progress_bar,
          " Issue information on number of VCs proved";
   "--show-tag", Arg.Set opt_show_tag,
          " Add a unique tag at the end of each error message";
   "--debug", Arg.Set opt_debug,
          " Enable debug mode";
]

let filename =
   let is_not_why_loc s =
      not (Filename.check_suffix s "why" ||
           Filename.check_suffix s "mlw") in
   Arg.parse options set_filename usage_msg;
   match !opt_filename with
   | None -> Gnat_util.abort_with_message "No file given."
   | Some s ->
         if is_not_why_loc s then
            Gnat_util.abort_with_message
              (Printf.sprintf "Not a Why input file: %s." s);
         s

let config =
   (* if a prover was given, read default config file and local config file *)
   try
      if !opt_prover = None then Whyconf.read_config (Some "why3.conf")
      else begin
         let conf = Whyconf.read_config None in
         Whyconf.merge_config conf gnatprove_why3conf_file
      end
   with Rc.CannotOpen _ ->
      Gnat_util.abort_with_message "Cannot read file why3.conf."

let config_main = Whyconf.get_main (config)

let env =
   Env.create_env (Whyconf.loadpath config_main)

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

(* loading the driver driver *)
let prover_driver : Driver.driver =
  try
    Driver.load_driver env prover.Whyconf.driver
      prover.Whyconf.extra_drivers
  with e ->
    Format.eprintf "Failed to load driver for prover: %a"
       Exn_printer.exn_printer e;
    Gnat_util.abort_with_message ""

(* freeze values *)

let timeout =
   match !opt_timeout with
   | Some x -> x
   | None ->
         if !opt_steps <> None then 0
         else default_timeout

let verbose = !opt_verbose
let report  = !opt_report
let proof_mode = !opt_proof_mode
let debug = !opt_debug
let force = !opt_force
let show_tag = !opt_show_tag
let split_name = "split_goal"
let limit_line = !opt_limit_line

let limit_subp =
   match !opt_limit_subp with
   | None -> None
   | Some s -> Some (Ident.create_label ("GP_Subp:" ^ s))

let ide_progress_bar = !opt_ide_progress_bar
let parallel = !opt_parallel

(* when not doing proof, stop after typing to avoid the exponential WP work *)
let () = if proof_mode = No_WP then Debug.set_flag Typing.debug_type_only
let () =
  if proof_mode <> Path_WP then
    Debug.set_flag (Debug.lookup_flag "fast_wp")
