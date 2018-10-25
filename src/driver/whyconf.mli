(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Managing the configuration of Why3 *)

open Wstdlib

(** {2 General configuration} *)

type config
(** A configuration linked to an rc file. Whyconf gives access to
    every sections of the rc file ({!Whyconf.get_section},
    {!Whyconf.set_section}, {!Whyconf.get_family},
    {!Whyconf.set_family}) but the section main and the family prover
    which are dealt by it ({!Whyconf.get_main}, {!Whyconf.set_main},
    {!Whyconf.get_provers}, {!Whyconf.set_provers} *)

exception ConfigFailure of string (* filename *) * string
exception DuplicateShortcut of string

val read_config : string option -> config
(** [read_config conf_file] :
    - If conf_file is given, then
      - if it is an empty string, an empty config is loaded,
      - if the file doesn't exist, Rc.CannotOpen is raised,
      - otherwise the content of the file is parsed and returned.
    - If conf_file is None and the WHY3CONFIG environment
      variable exists, then the above steps are executed with
      the content of the variable (possibly empty).
    - If neither conf_file nor WHY3CONFIG are present, the file
      "$HOME/.why3.conf" (or "$USERPROFILE/.why3.conf" under
      Windows) is checked for existence:
      - if present, the content is parsed and returned,
      - otherwise, we return the built-in default_config with a
        default configuration filename. *)

val merge_config : config -> string -> config
(** [merge_config config filename] merge the content of [filename]
    into [config] *)

val save_config : config -> unit
(** [save_config config] save the configuration *)

val default_config : string -> config
(** [ default_config filename ] create a default configuration which is going
    to be saved in [ filename ]*)

val get_conf_file : config -> string
(** [get_conf_file config] get the rc file corresponding to this
    configuration *)
(* val set_conf_file : config -> string -> config *)
(* (\** [set_conf_file config] set the rc file corresponding to this *)
(*     configuration *\) *)

(** {2 Main section} *)
type main

val get_main : config -> main
(** [get_main config] get the main section stored in the Rc file *)

val set_main : config -> main -> config
(** [set_main config main] replace the main section by the given one *)

val libobjdir: main -> string

val libdir: main -> string
val datadir: main -> string
val loadpath: main -> string list
val set_loadpath : main -> string list -> main
val default_loadpath : string list
val timelimit: main -> int
val memlimit: main -> int
val running_provers_max: main -> int
val set_limits: main -> int -> int -> int -> main

val default_editor: main -> string
(** editor name used when no specific editor known for a prover *)
val set_default_editor: main -> string -> main

val plugins : main -> string list
val pluginsdir : main -> string
val set_plugins : main -> string list -> main
val add_plugin : main -> string -> main
val load_plugins : main -> unit

(** {2 Provers} *)

(** {3 Prover's identifier} *)

type prover = {
  prover_name : string; (* "Alt-Ergo" *)
  prover_version : string; (* "2.95" *)
  prover_altern : string; (* "special" *)
}
    (** record of necessary data for a given external prover *)

val print_prover : Format.formatter -> prover -> unit
val print_prover_parseable_format : Format.formatter -> prover -> unit
val prover_parseable_format : prover -> string

(** Printer for prover *)
module Prover   : OrderedHashedType with type t = prover
module Mprover  : Extmap.S with type key = prover
module Sprover  : Extset.S with module M = Mprover
module Hprover  : Exthtbl.S with type key = prover

(** {3 Prover configuration} *)

type config_prover = {
  prover       : prover;   (* unique name for session *)
  command      : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  command_steps: string option; (* The command when the number of steps is limited "exec why-limit %t %m -steps-bound %S alt-ergo %f"  *)
  driver       : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  in_place     : bool;     (* verification should be performed in-place *)
  editor       : string;   (* Dedicated editor *)
  interactive  : bool; (* Interactive theorem prover *)
  extra_options: string list;
  extra_drivers: string list;
  configure_build : string; (* Added for spark, default = "" *)
  build_commands : string list; (* Added for spark, default = [] *)
}

val get_complete_command : config_prover -> with_steps:bool -> string
(** add the extra_options to the command *)

val get_provers : config -> config_prover Mprover.t
(** [get_provers config] get the prover family stored in the Rc file. The
    keys are the unique ids of the prover (argument of the family) *)

val get_prover_config: config -> prover -> config_prover
(** [get_prover_config config prover] get the prover config as stored in
 the config. Raise Not_found if the prover does not exists in the config. *)

val set_provers : config ->
  ?shortcuts:prover Mstr.t -> config_prover Mprover.t -> config
(** [set_provers config provers] replace all the family prover by the
    one given *)

val is_prover_known : config -> prover -> bool
(** test if a prover is detected *)

val get_prover_shortcuts : config -> prover Mstr.t
(** return the prover shortcuts *)

val set_prover_shortcuts : config -> prover Mstr.t -> config
(** set the prover shortcuts *)

type config_editor = {
  editor_name : string;
  editor_command : string;
  editor_options : string list;
}

module Meditor : Extmap.S with type key = string

val set_editors : config -> config_editor Meditor.t -> config
(** replace the set of editors *)

val get_editors : config -> config_editor Meditor.t
(** returns the set of editors *)

val editor_by_id : config -> string -> config_editor
(** return the configuration of the editor if found, otherwise return
    Not_found *)

(** prover upgrade policy *)

type prover_upgrade_policy =
  | CPU_keep
  | CPU_upgrade of prover
  | CPU_duplicate of prover
  | CPU_remove

val print_prover_upgrade_policy : Format.formatter -> prover_upgrade_policy -> unit

val set_prover_upgrade_policy :
  config -> prover -> prover_upgrade_policy -> config
(** [set_prover_upgrade c p cpu] sets or updates the policy to follow if the
    prover [p] is absent from the system *)

val get_prover_upgrade_policy : config -> prover -> prover_upgrade_policy
(** [get_prover_upgrade config] returns a map providing the policy to
    follow for each absent prover (if it has already been decided
    by the user and thus stored in the config) *)

val get_policies : config -> prover_upgrade_policy Mprover.t

val set_policies : config -> prover_upgrade_policy Mprover.t -> config

(** strategies *)

type config_strategy = {
  strategy_name : string;
  strategy_desc : string;
  strategy_code : string;
  strategy_shortcut : string;
}

val get_strategies : config -> config_strategy Mstr.t

val add_strategy : config -> config_strategy -> config

(** filter prover *)
type filter_prover

val mk_filter_prover :
  ?version:string -> ?altern:string -> (* name *) string -> filter_prover

val print_filter_prover :
  Format.formatter -> filter_prover -> unit

val parse_filter_prover : string -> filter_prover
(** parse the string representing a filter_prover:
    - "name,version,altern"
    - "name,version" -> "name,version,^.*"
    - "name,,altern" -> "name,^.*,altern"
    - "name" -> "name,^.*,^.*"

    regexp must start with ^. Partial match will be used.
*)

val filter_prover_with_shortcut : config -> filter_prover -> filter_prover
(** resolve prover shortcut in filter *)

val filter_prover : filter_prover -> prover -> bool
(** test if the prover match the filter prover *)

val filter_provers : config -> filter_prover -> config_prover Mprover.t
(** Get all the provers that match this filter *)

exception ProverNotFound  of config * filter_prover
exception ProverAmbiguity of config * filter_prover * config_prover  Mprover.t
exception ParseFilterProver of string

val filter_one_prover : config -> filter_prover -> config_prover
(** find the uniq prover that verify the filter. If it doesn't exists
    raise ProverNotFound or raise ProverAmbiguity *)

val why3_regexp_of_string : string -> Str.regexp

(** {2 For accesing other parts of the configuration } *)

val get_section : config -> string -> Rc.section option
(** [get_section config name] Same as {!Rc.get_section} except name
    must not be "main" *)
val get_family  : config -> string -> Rc.family
(** [get_family config name] Same as {!Rc.get_family} except name
    must not be prover *)

val set_section : config -> string -> Rc.section -> config
(** [set_section config name] Same as {!Rc.set_section} except name
    must not be "main" *)
val set_family  : config -> string -> Rc.family  -> config
(** [set_family config name] Same as {!Rc.set_family} except name
    must not be prover *)

(** Common command line options *)

module Args : sig

  val initialize :
    ?extra_help : (Format.formatter -> unit -> unit) ->
    (string * Arg.spec * string) list ->
    (string -> unit) -> string ->
    config * config * Env.env

  val exit_with_usage :
    ?exit_code : int ->
    ?extra_help : (Format.formatter -> unit -> unit) ->
    (string * Arg.spec * string) list -> string -> 'a

end


(** Loading drivers with relative names *)

val load_driver : main -> Env.env -> string -> string list -> Driver.driver
(** wrapper for loading a driver from a file that may be relative to the datadir.
    See [Driver.load_driver_absolute]
*)

val unknown_to_known_provers  :
  config_prover Mprover.t -> prover ->
  prover list * prover list * prover list
(** return others, same name, same version *)
