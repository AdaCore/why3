(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
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
end

module Detected_binary: sig
  type t
end

module Manual_binary: sig
  type t = {
    same_as  : string;
    binary : string; (* custom executable *)
    shortcut: string option;
  }

  val add: Whyconf.config -> t -> Whyconf.config
  (** Add the given manual binary to the user configuration and remove the previous one that had the same shortcut *)
end

val read_auto_detection_data: Whyconf.config -> Prover_autodetection_data.t

type binaries

(** Detect the provers *)
val request_binaries_version :
  Whyconf.config -> Prover_autodetection_data.t -> binaries

val request_manual_binaries_version :
  Prover_autodetection_data.t -> Manual_binary.t list ->
  binaries

val set_binaries_detected:
  binaries -> Whyconf.config -> Whyconf.config
(** replace all the binaries detected by the given one in the configuration *)

val update_binaries_detected:
  binaries -> Whyconf.config -> Whyconf.config
(** replace or add only the binaries detected by the given one in the
    configuration *)

val compute_builtin_prover:
  binaries ->
  Prover_autodetection_data.t ->
  Whyconf.config_prover Whyconf.Mprover.t
(** Compute the builtin prover. Only print errors if {!is_config_command} is
   false *)
