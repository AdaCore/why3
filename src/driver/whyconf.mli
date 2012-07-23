(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Managing the configuration of Why3 *)

open Util

(** {2 General configuration} *)

type config
(** A configuration linked to an rc file. Whyconf gives access to
    every sections of the rc file ({!Whyconf.get_section},
    {!Whyconf.set_section}, {!Whyconf.get_family},
    {!Whyconf.set_family}) but the section main and the family prover
    which are dealt by it ({!Whyconf.get_main}, {!Whyconf.set_main},
    {!Whyconf.get_provers}, {!Whyconf.set_provers} *)

exception ConfigFailure of string (* filename *) * string

val read_config : string option -> config
(** [read_config conf_file] :
    - If conf_file is given and the file doesn't exist Rc.CannotOpen is
    raised.
    - If "$WHY3CONFIG" is given and the file doesn't exist Rc.CannotOpen
    is raised
    - otherwise we try reading "$HOME/.why3.conf" (or
    "$USERPROFILE/.why3.conf" under Windows) and, if not present, we return
    the built-in default_config with default configuration filename *)

val merge_config : config -> string -> config
(** [merge_config config filename] merge the content of [filename]
    into [config]( *)

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

val get_main    : config  -> main
(** [get_main config] get the main section stored in the Rc file *)

val set_main    : config -> main                 -> config
(** [set_main config main] replace the main section by the given one *)

val libdir: main -> string
val datadir: main -> string
val loadpath: main -> string list
val timelimit: main -> int
val memlimit: main -> int
val running_provers_max: main -> int
val set_limits: main -> int -> int -> int -> main

val plugins : main -> string list
val pluginsdir : main -> string
val set_plugins : main -> string list -> main
val add_plugin : main -> string -> main
val load_plugins : main -> unit

(** {2 Provers} *)

(** {3 Prover's identifier} *)

type prover =
    { prover_name : string; (* "Alt-Ergo" *)
      prover_version : string; (* "2.95" *)
      prover_altern : string; (* "special" *)
    }
    (** record of necessary data for a given external prover *)

val print_prover : Format.formatter -> prover -> unit
val print_prover_parsable_format : Format.formatter -> prover -> unit

(** Printer for prover *)
module Prover   : Util.OrderedHash with type t = prover
module Mprover  : Stdlib.Map.S with type key = prover
module Sprover  : Mprover.Set
module Hprover  : Hashtbl.S with type key = prover

(** {3 Prover configuration} *)

type config_prover = {
  prover : prover;  (* unique name for session *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  in_place: bool;     (* verification should be performed in-place *)
  editor  : string;   (* Dedicated editor *)
  interactive : bool; (* Interactive theorem prover *)
  extra_options : string list;
  extra_drivers : string list;
}

val get_provers : config  -> config_prover Mprover.t
(** [get_provers config] get the prover family stored in the Rc file. The
    keys are the unique ids of the prover (argument of the family) *)

val set_provers : config -> config_prover Mprover.t -> config
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

module Meditor : Stdlib.Map.S with type key = string

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

val filter_prover : filter_prover -> prover -> bool
(** test if the prover match the filter prover *)

val filter_provers : config -> filter_prover -> config_prover Mprover.t
(** test if the prover match the filter prover *)

exception ProverNotFound  of config * filter_prover
exception ProverAmbiguity of config * filter_prover * config_prover  Mprover.t
exception ParseFilterProver of string

val filter_one_prover : config -> filter_prover -> config_prover
(** find the uniq prover that verify the filter. If it doesn't exists
    raise ProverNotFound or raise ProverAmbiguity *)

val why3_regexp_of_string : string -> Str.regexp

(** {2 For accesing other parts of the configuration } *)

(** Access to the Rc.t *)
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
