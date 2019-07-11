open Why3

val abort_with_message : internal:bool -> string -> 'a
(* print a JSON record that consists of an error message and exit.
   internal = true   - an internal error that should be reported using a bugbox
   internal = false  - a "real" error that should be reported normally
*)

val colon_split : string -> string list
(* split the given string at the character ':' *)

val get_gnatprove_config : ?extra_conf_file:string -> Whyconf.config -> Whyconf.config
(* rewrite driver information in the prover information to be suitable for
   gnatprove. The location of an additional config file may be used for
   this.  *)

val why3_prefix : string
val spark_prefix : string
(* executable is in <prefix>/libexec/spark/bin
   why3-prefix is <prefix>/libexec/spark
   spark-prefix is <prefix> *)

val gnatprove_why3conf_file : string

val file_concat : string list -> string
(* use Filename.concat to construct the string a/b/c/d from [a;b;c;d] *)

val spark_loadpath : string list
(* list of paths to search for why3 library files *)

val build_env_from_config :
  load_plugins:bool -> proof_dir:string option -> Whyconf.config -> Env.env
(* Build an environment with the correct loadpaths from a config.
   load_plugins - if plug-ins should be loaded
   proof_dir    - if present, the path proof_dir/_theories is added to the
                  loadpath *)

val set_debug_flags_gnatprove : unit -> unit
(* set the debug flags for a normal operation of gnatprove *)
