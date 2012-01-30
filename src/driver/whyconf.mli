(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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
(** Printer for prover *)
module Prover   : Util.OrderedHash with type t = prover
module Mprover  : Stdlib.Map.S with type key = prover
module Sprover  : Mprover.Set
module Hprover  : Hashtbl.S with type key = prover

(** {3 Prover configuration} *)

type config_prover = {
  prover : prover;  (* unique name for session *)
  id      : string; (* unique name for command line *)
  command : string;   (* "exec why-limit %t %m alt-ergo %f" *)
  driver  : string;   (* "/usr/local/share/why/drivers/ergo-spec.drv" *)
  editor  : string;   (* Dedicated editor *)
  interactive : bool; (* Interative theorem prover *)
}

val get_provers : config  -> config_prover Mprover.t
(** [get_main config] get the prover family stored in the Rc file. The
    keys are the unique ids of the prover (argument of the family) *)

val set_provers : config -> config_prover Mprover.t -> config
(** [set_provers config provers] replace all the family prover by the
    one given *)

val is_prover_known : config -> prover -> bool
(** test if a prover is detected *)

exception ProverNotFound of config * string
exception ProverAmbiguity of config * string * prover list

val prover_by_id : config -> string -> config_prover

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
