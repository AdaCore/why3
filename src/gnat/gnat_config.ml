open Why3

type report_mode = Fail | Verbose | Detailed

let opt_verbose = ref false
let opt_timeout = ref 10
let opt_steps = ref 0
let opt_report = ref Fail
let opt_debug = ref false
let opt_force = ref false
let opt_filename : string option ref = ref None

let set_filename s =
   if !opt_filename = None then
      opt_filename := Some s
   else
      Gnat_util.abort_with_message "Only one file name should be given."

let set_report s =
   if s = "detailed" then
      opt_report := Detailed
   else if s = "all" then
      opt_report := Verbose
   else if s <> "fail" then
      Gnat_util.abort_with_message
        "argument for option --report should be one of (fail|all|detailed)."


let usage_msg =
  "Usage: gnatwhy3 [options] file"

let options = Arg.align [
   "-v", Arg.Set opt_verbose, "Output extra verbose information";
   "--verbose", Arg.Set opt_verbose, "Output extra verbose information";

   "-t", Arg.Set_int opt_timeout,
          "Set the timeout in seconds (default is 10 seconds)";
   "--timeout", Arg.Set_int opt_timeout,
          "Set the timeout in seconds (default is 10 seconds)";

   "-s", Arg.Set_int opt_steps,
          "Set the maximal number of proof steps";
   "--steps", Arg.Set_int opt_steps,
          "Set the maximal number of proof steps";
   "-f", Arg.Set opt_force,
          "Rerun VC generation and proofs, even when the result is up to date";
   "--force", Arg.Set opt_force,
          "Rerun VC generation and proofs, even when the result is up to date";
   "--report", Arg.String set_report,
          "set report mode, one of (fail | all | detailed), default is fail";
   "--debug", Arg.Set opt_debug,
          "Enable debug mode";
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

let result_file =
   let base = Filename.chop_extension filename in
   base ^ ".proof"

let report_mode =
   if !opt_force then false
   else
      if Sys.file_exists result_file then begin
         if Gnat_util.cmp_timestamps filename result_file < 0 then begin
            if !opt_verbose then
               Format.printf "gnatwhy3: entering report mode@.";
            true
         end else begin
            if !opt_verbose then
               Format.printf "gnatwhy3: result file older than input file@.";
            false
         end
      end else begin
         if !opt_verbose then
            Format.printf "gnatwhy3: result file does not exist@.";
         false
      end

let config =
   try Whyconf.read_config (Some "why3.conf")
   with Rc.CannotOpen _ ->
      Gnat_util.abort_with_message "Cannot read file why3.conf."

let config_main = Whyconf.get_main (config)

let env =
   Env.create_env (Whyconf.loadpath config_main)

let provers : Whyconf.config_prover Util.Mstr.t =
   Whyconf.get_provers config

let alt_ergo : Whyconf.config_prover =
  try
    Util.Mstr.find "alt-ergo" provers
  with Not_found ->
    Gnat_util.abort_with_message
      "Prover alt-ergo not installed or not configured."

(* loading the Alt-Ergo driver *)
let altergo_driver : Driver.driver =
  try
    Driver.load_driver env alt_ergo.Whyconf.driver
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a"
       Exn_printer.exn_printer e;
    Gnat_util.abort_with_message ""

let alt_ergo_command =
   let command = alt_ergo.Whyconf.command in
   if !opt_steps = 0 then command
   else command ^ Printf.sprintf " -steps %d" !opt_steps

let split_trans = Trans.lookup_transform_l "split_goal" env

(* freeze values *)

let timeout = !opt_timeout
let verbose = !opt_verbose
let report  = !opt_report
let debug = !opt_debug
let force = !opt_force
