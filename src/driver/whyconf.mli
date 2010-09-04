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

val sharedir : string (* For image, ... *)

type config_prover = {
  name    : string;   (* "Alt-Ergo v2.95 (special)" *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  version : string;   (* "v2.95" *)
  editor  : string;   (* Interative theorem prover *)
}

type main = {
  loadpath  : string list;  (* "/usr/local/share/why/theories" *)
  timelimit : int;   (* default prover time limit in seconds
                               (0 unlimited) *)
  memlimit  : int;
  (* default prover memory limit in megabytes (0 unlimited)*)
  running_provers_max : int;
  (* max number of running prover processes *)
}

type config = {
  conf_file : string;       (* "/home/innocent_user/.why.conf" *)
  config    : Rc.t;
}

val default_config : config

(** if conf_file is not given, tries the following:
   "$WHY_CONFIG"; "./why.conf"; "./.why.conf";
   "$HOME/.why.conf"; "$USERPROFILE/.why.conf" *)
val read_config : string option -> config

val save_config : config -> unit

val get_main    : config  -> main
val get_provers : config  -> config_prover Mstr.t

val set_main    : config -> main                 -> config
val set_provers : config -> config_prover Mstr.t -> config


(** Replace the provers by autodetected one *)
val run_auto_detection : unit -> config_prover Mstr.t
