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
}

type config = {
  conf_file : string;       (* "/home/innocent_user/.why.conf" *)
  loadpath  : string list;  (* "/usr/local/share/why/theories" *)
  timelimit : int option;   (* default prover time limit in seconds *)
  memlimit  : int option;   (* default prover memory limit in megabytes *)
  provers   : config_prover Mstr.t;   (* indexed by short identifiers *)
}

(** if conf_file is not given, tries the following:
   "$WHY_CONFIG"; "./why.conf"; "./.why.conf";
   "$HOME/.why.conf"; "$USERPROFILE/.why.conf" *)
val read_config : string option -> config

val save_config : config -> unit

(** error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

