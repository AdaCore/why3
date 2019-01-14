open Why3

(* Configuration settings given why3.conf file and command line options *)

val config : Whyconf.config
val env : Env.env

val provers : Whyconf.prover list
(* the provers, either the default prover, or as given by --prover *)

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

val steps : prover : string -> int
(* value of the --steps option adjusted for given prover, if no steps are
 * given, return None *)

val back_convert_steps : prover : string -> int -> int
(* given the raw steps a prover has taken, reconvert them to SPARK steps *)

val limit : prover : string -> warning:bool -> Call_provers.resource_limit

type proof_mode =
    Progressive
  | No_WP
  | All_Split
  | Per_Path
  | Per_Check

type limit_mode =
  | Limit_Check of Gnat_expl.check
  | Limit_Line of Gnat_loc.loc
(* This type is used only to differenciate the two different uses of
   --limit-line: - --limit-line=file:line -> Limit_Line
                 - --limit-line=file:line:checkkind -> Limit_Check *)

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

val limit_line : limit_mode option
(* set if option --limit-line was given; we only prove VCs from that line *)

val limit_region : Gnat_loc.region option
(* set if option --limit-region was given; we only prove VCs in the region *)

val limit_subp : Ident.attribute option
(* set if option --limit-subp was given; we only prove VCs from that subprogram
   *)

val parallel : int
(* number of parallel processes that can be run in parallel for proving VCs *)

val socket_name : string
(* name of the socket to be used for communication with the server *)

val proof_dir : string option

val actual_cmd : ?main:Whyconf.main -> string -> string -> string
(* [actual_cmd main filename cmd] replaces the different '%'
   preceded terms in [cmd] by their corresponding values *)

val replay : bool
