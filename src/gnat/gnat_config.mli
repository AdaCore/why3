open Why3

(* Configuration settings given more or less by the why3.conf file *)

val config : Whyconf.config
val env : Env.env
val prover_driver : Driver.driver
val prover : Whyconf.config_prover
val prover_editor : unit -> Whyconf.config_editor

(* Configuration settings given or determined by the command line *)

val timeout : int
(* value of the -t/--timeout option, default value 10 *)

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

type limit_mode =
  | Limit_Check of Gnat_expl.check
  | Limit_Line of Gnat_loc.loc
(* This type is used only to differenciate the two different uses of
   --limit-line: - --limit-line=file:line -> Limit_Line
                 - --limit-line=file:line:checkkind -> Limit_Check *)

val proof_mode : proof_mode
(* reflects value of option --proof, default "Then_Split" *)

val debug : bool
(* true if option --debug was present *)

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

val limit_subp : Ident.label option
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
