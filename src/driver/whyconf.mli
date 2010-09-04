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

(** Manage the config file of Why *)

open Util

type config_prover = {
  name    : string;   (* "Alt-Ergo v2.95 (special)" *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  version : string;   (* "v2.95" *)
  editor  : string;   (* Interative theorem prover *)
}

type main = {
  libdir   : string;      (* "/usr/local/lib/why/" *)
  datadir  : string;      (* "/usr/local/share/why/" *)
  loadpath  : string list;  (* "/usr/local/lib/why/theories" *)
  timelimit : int;   (* default prover time limit in seconds
                               (0 unlimited) *)
  memlimit  : int;
  (* default prover memory limit in megabytes (0 unlimited)*)
  running_provers_max : int;
  (* max number of running prover processes *)
}

type config

(** - If conf_file is given and the file doesn't exists Not_found is
    raised.
    - If "$WHY_CONFIG" is given and the file doesn't exists Not_found is raised
    - otherwise tries the following:
    "./why.conf"; "./.why.conf"; "$HOME/.why.conf";
    "$USERPROFILE/.why.conf"; the built-in default_config *)
val read_config : string option -> config
val save_config : config -> unit
val default_config : string -> config

val get_main    : config  -> main
val get_provers : config  -> config_prover Mstr.t

val set_main    : config -> main                 -> config
val set_provers : config -> config_prover Mstr.t -> config

val set_conf_file : config -> string -> config
val get_conf_file : config -> string

val get_section : config -> string -> Rc.section option
val get_family  : config -> string -> Rc.family

val set_section : config -> string -> Rc.section -> config
val set_family  : config -> string -> Rc.family  -> config

