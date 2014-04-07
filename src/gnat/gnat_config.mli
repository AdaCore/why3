open Why3

(* Configuration settings given more or less by the why3.conf file *)

val config : Whyconf.config
val env : Env.env
val prover_driver : Driver.driver
val prover : Whyconf.config_prover

(* Configuration settings given or determined by the command line *)

val timeout : int
(* value of the -t/--timeout option, default value 10 *)

type verbosity =
  | Normal
  | Quiet
  | Verbose

val verbose : verbosity
(* true if option -v/--verbose was present *)

type report_mode = Fail | Fail_And_Proved | Statistics
(* In mode fail, only print failed proof objectives.
   In mode fail_and_proved, print all proof objectives.
   In mode statistics, additionally print steps and time taken by the VC *)

type proof_mode =
    Then_Split
  | No_WP
  | All_Split
  | Path_WP
  | No_Split
(* In mode normal, compute VCs and split VCs as necessary, call prover as
                   necessary;
   In mode no_wp, do not compute VCs and never call the prover
   In mode all_split, compute all split VCs, and never call the prover
   In mode Path_WP, use the "normal WP" to compute one VC for each path
   In mode No_Split, do not split VCs at all
   *)

type warning_mode =
  | Suppress
  | Warn_Normal
  | Treat_As_Error
(* In mode Warn_Normal, exit code of gnatwhy3 is always 0; In mode
   Treat_As_Error, exit code of gnatwhy3 is non-zero when unproved checks
   exist, 0 otherwise.  Mode Suppress is ignored by gnatwhy3 (behaves like mode
   Warn_Normal). Default is Treat_As_Error. *)

val report : report_mode
(* reflects value of option --report, default "Fail" *)

val proof_mode : proof_mode
(* reflects value of option --proof, default "Then_Split" *)

val warning_mode : warning_mode

val debug : bool
(* true if option --debug was present *)

val force : bool
(* true of option --force/-f was present *)

(* Configuration settings related to input and output *)

val filename : string
(* the name of the input file *)

val unit_name : string
(* the name of the Ada unit to which the input file corresponds *)

val limit_line : Gnat_loc.loc option
(* set if option --limit-line was given; we only prove VCs from that line *)

val limit_subp : Ident.label option
(* set if option --limit-subp was given; we only prove VCs from that subprogram
   *)

val ide_progress_bar : bool
(* set if option --ide-progress-bar was given, to issue formatted output on
   current numbers of VCs proved *)

val parallel : int
(* number of parallel processes that can be run in parallel for proving VCs *)

val socket_name : string
(* name of the socket to be used for communication with the server *)
