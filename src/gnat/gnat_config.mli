open Why3

(* Configuration settings given why3.conf file and command line options *)

val config : Whyconf.config
val env : Env.env

val provers : Whyconf.prover list
(* the provers, either the default prover, or as given by --prover *)

val session_dir : string
val session_file : string
(* the directory in which the session file is stored, and the session file itself *)

val is_selected_prover : Whyconf.prover -> Whyconf.prover option
(* test if the given prover is a selected prover, i.e. in the [provers] list
   above *)

val prover_ce : Whyconf.prover option
(* the prover for counterexamples generation
   None if counterexample should not be generated
*)

val prover_warn : Whyconf.prover option
(* the prover for warning VCs
   None if warning VCs should be ignored
*)

val is_ce_prover : Session_itp.session -> Session_itp.proofAttemptID -> bool
(* check if the prover in argument is the prover for counter examples. returns
 * false if no prover is selected for counterexamples, or counterexamples are
 * off *)

val counterexamples : bool
(* Reflects the value of the option --counterexample, default off
   Counter examples are also disabled when CVC4 is not found *)

val manual_prover : Whyconf.prover option
(* Currently, if a manual prover is provided, it must be the only one. So in
   when dealing with manual proof, it makes sense to speak of "the prover" *)

(* Configuration settings given or determined by the command line *)

val steps: config_prover:Whyconf.config_prover -> int
(* value of the --steps option adjusted for given prover config, if no steps are
 * given, return 0 *)

val back_convert_steps : prover : string -> int -> int
(* given the raw steps a prover has taken, reconvert them to SPARK steps *)

val limit: prover:Whyconf.prover -> warning:bool -> Call_provers.resource_limit

type proof_mode =
    Progressive
  | No_WP
  | All_Split
  | Per_Path
  | Per_Check

val proof_mode : proof_mode
(* reflects value of option --proof, default "Then_Split" *)

val lazy_ : bool

val debug : bool
(* true if option --debug was present *)

val debug_save_vcs : bool
(* true if option --debug-save-vcs was present *)

val stand_alone : bool
(* true if option --standalone was present *)

val force : bool
(* true of option --force/-f was present *)

(* Configuration settings related to input and output *)

val filename : string
(* the name of the input file *)

val unit_name : string
(* the name of the Ada unit to which the input file corresponds *)

val limit_line : Gnat_expl.limit_mode option
(* set if option --limit-line was given; we only prove VCs from that line *)

val limit_region : Gnat_loc.region option
(* set if option --limit-region was given; we only prove VCs in the region *)

val parallel : int
(* number of parallel processes that can be run in parallel for proving VCs *)

val socket_name : string
(* name of the socket to be used for communication with the server *)

val proof_dir : string option

val actual_cmd : ?main:Whyconf.main -> string -> string -> string
(* [actual_cmd main filename cmd] replaces the different '%'
   preceded terms in [cmd] by their corresponding values *)

val replay : bool
