(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Whyconf

val verbose: Debug.flag

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

(** {2 Spec for version, debug} *)
(* val simple_spec : spec_list *)

(*
val read_simple_spec : unit -> bool
(** return if we must exit *)
*)

(** {2 Spec for configuration, loadpath} *)
val common_options : spec_list

val read_env_spec : unit -> Env.env * Whyconf.config * bool
(** read_simple_spec also *)

val read_update_session :
  allow_obsolete:bool -> Env.env ->
  Whyconf.config -> string ->
  unit Session.env_session * bool * bool

(** {2 Spec for filtering } *)
type filter_prover

val read_opt_prover : string -> filter_prover
val prover_of_filter_prover : config -> filter_prover -> Why3.Whyconf.prover
val provers_of_filter_prover : config -> filter_prover -> Why3.Whyconf.Sprover.t

type filters

val filter_spec : spec_list

val read_filter_spec : Whyconf.config -> filters * bool

val theory_iter_proof_attempt_by_filter :
  filters ->
  ('key Session.proof_attempt -> unit) -> 'key Session.theory -> unit
val session_iter_proof_attempt_by_filter :
  filters ->
  ('key Session.proof_attempt -> unit) -> 'key Session.session -> unit


(* quite ad-hoc *)
type filter_three = | FT_Yes | FT_No | FT_All
val set_filter_verified_goal : filter_three -> unit

(** force obsolete *)
val opt_force_obsolete : bool ref
val force_obsolete_spec : spec_list


(** ask yes/no question to the user *)
val ask_yn : unit -> bool

val ask_yn_nonblock : callback:(bool -> unit) -> (unit -> bool)
(** call the callback when an answer have been given,
    return true if it must be retried *)
