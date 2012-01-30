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

open Why3
open Whyconf

type spec_list = (Arg.key * Arg.spec * Arg.doc) list

type cmd =
    {
      cmd_spec : spec_list;
      cmd_desc : string;
      cmd_name : string;
      cmd_run  : unit -> unit;
    }



(** {2 Anonymous argument} *)
val iter_files : (string -> unit) -> unit
val anon_fun : Arg.anon_fun

(** print_version *)
val print_version : unit -> unit


(** {2 Spec for version, debug} *)
val simple_spec : spec_list

val read_simple_spec : unit -> bool
(** return if we must exit *)

(** {2 Spec for configuratio, loadpath} *)
val env_spec : spec_list
(** include simple_spec *)

val read_env_spec : unit -> Env.env * Whyconf.config * bool
(** read_simple_spec also *)

val read_update_session :
  allow_obsolete:bool ->
  Why3.Env.env ->
  Why3.Whyconf.config -> string -> unit Why3.Session.env_session * bool

(** {2 Spec for filtering } *)
type filter_prover =
  | Prover of Whyconf.prover
  | ProverId of string

val read_opt_prover : string -> filter_prover
val prover_of_filter_prover : config -> filter_prover -> prover

type filters = Sprover.t (* if empty : every provers *)
    (* * ... *)

val filter_spec : spec_list

val read_filter_spec : Whyconf.config -> filters * bool

val session_iter_proof_attempt_by_filter :
  filters ->
  ('key Session.proof_attempt -> unit) -> 'key Session.session -> unit
