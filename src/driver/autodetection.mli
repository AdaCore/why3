(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val debug: Debug.flag

(* If true make the autodetection verbose *)
val is_config_command: bool ref

(** Lists binarires names looked for from detection config *)
val list_binaries : unit -> string list

(** Adds a new prover executable *)
(* val add_prover_binary :
 *   Whyconf.config -> string -> string -> string -> Whyconf.config *)

module Prover_autodetection_data: sig
  type t
  val from_file: string -> t
end

module Partial: sig

  type t = {
    name : string;
    path : string;
    version : string;
    shortcut : string option;
    manual : bool;
  }
end

val read_auto_detection_data: Whyconf.config -> Prover_autodetection_data.t

val find_prover : Prover_autodetection_data.t -> string -> string -> string option
(** [find_prover data name path] returns the prover version of [path], if any,
    according to an entry about [name] in [data] *)

val find_provers : Prover_autodetection_data.t -> (string * string * string) list
(** Detect the provers and return their path, name, and versions.
    The resulting list is sorted by names and versions. *)

val remove_auto_provers: Whyconf.config -> Whyconf.config
(** Remove all the non-manual provers from the configuration *)

val update_provers: Partial.t list -> Whyconf.config -> Whyconf.config
(** Replace or add the given provers in the configuration *)

val compute_builtin_prover:
  Partial.t list ->
  Whyconf.config ->
  Prover_autodetection_data.t ->
  Whyconf.config_prover Whyconf.Mprover.t
(** Compute the builtin prover. Only print errors if {!is_config_command} is
   false *)
