open Why3

(* Configuration settings given more or less by the why3.conf file *)

val env : Env.env
val split_trans : Task.task Trans.tlist
val alt_ergo_command : string
val altergo_driver : Driver.driver

(* Configuration settings given or determined by the command line *)

val timeout : int
(* value of the -t/--timeout option, default value 10 *)

val verbose : bool
(* true if option -v/--verbose was present *)

type report_mode = Fail | Verbose | Detailed
(* In mode fail, only print failed proof objectives.
   In mode verbose, print all proof objectives.
   In mode detailed, additionally print if VC was timeout or if prover stopped.
   *)

val report : report_mode
(* true if option --report was present *)

val debug : bool
(* true if option --debug was present *)

(* Configuration settings related to input and output *)

val result_file : string
(* the name of the output file *)

val filename : string
(* the name of the input file *)

val report_mode : bool
(* true if the output file exists and is newer than the input file, and we are
 * not in force mode (--force or -f) *)

val noproof : bool
(* true if option --no-proof was present *)
