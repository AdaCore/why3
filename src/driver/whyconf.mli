(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

(** Managing the configuration of Why *)

open Util

type config_prover = {
  name    : string;   (* "Alt-Ergo v2.95 (special)" *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  version : string;   (* "v2.95" *)
  editor  : string;   (* Interative theorem prover *)
}

type main

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

type config
(** A configuration linked to an rc file. Whyconf gives access to
    every sections of the rc file ({!Whyconf.get_section},
    {!Whyconf.set_section}, {!Whyconf.get_family},
    {!Whyconf.set_family}) but the section main and the family prover
    which are dealt by it ({!Whyconf.get_main}, {!Whyconf.set_main},
    {!Whyconf.get_provers}, {!Whyconf.set_provers} *)

val read_config : string option -> config
(** [read_config conf_file] :
    - If conf_file is given and the file doesn't exists Not_found is
    raised.
    - If "$WHY_CONFIG" is given and the file doesn't exists Not_found is raised
    - otherwise tries the following, Not_found is never raised :
    "./why.conf"; "./.why.conf"; "$HOME/.why.conf";
    "$USERPROFILE/.why.conf"; the built-in default_config with default
    configuration filename*)

val save_config : config -> unit
(** [save_config config] save the configuration *)

val default_config : string -> config
(** [ default_config filename ] create a default configuration which is going
    to be saved in [ filename ]*)

val get_main    : config  -> main
(** [get_main config] get the main section stored in the Rc file *)
val get_provers : config  -> config_prover Mstr.t
(** [get_main config] get the prover family stored in the Rc file. The
    keys are the unique ids of the prover (argument of the family) *)

val set_main    : config -> main                 -> config
(** [set_main config main] replace the main section by the given one *)
val set_provers : config -> config_prover Mstr.t -> config
(** [set_provers config provers] replace all the family prover by the
    one given *)

val get_conf_file : config -> string
(** [get_conf_file config] get the rc file corresponding to this
    configuration *)
(* val set_conf_file : config -> string -> config *)
(* (\** [set_conf_file config] set the rc file corresponding to this *)
(*     configuration *\) *)

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
