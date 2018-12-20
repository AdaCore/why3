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

(** Lists prover family names from detection config *)
val list_prover_families : unit -> string list

(** Adds a new prover executable *)
val add_prover_binary :
  Whyconf.config -> string -> string -> string -> Whyconf.config

(** Replace the provers by autodetected one *)
val run_auto_detection : Whyconf.config -> Whyconf.config
