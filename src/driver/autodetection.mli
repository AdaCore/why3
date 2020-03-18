(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

val debug: Debug.flag
val is_config_command: bool ref

(** Lists prover family names from detection config *)
val list_prover_families : unit -> string list

(** Adds a new prover executable *)
val add_prover_binary :
  Whyconf.config -> string -> string -> string -> Whyconf.config

type autodetection_result

(** Detect the provers *)
val run_auto_detection : Whyconf.config -> autodetection_result

(** Replace the provers by autodetected one *)
val generate_builtin_config : autodetection_result -> Whyconf.config -> Whyconf.config

(** Replace the output of provers with the current one *)
val generate_detected_config : autodetection_result -> Whyconf.detected_prover list
