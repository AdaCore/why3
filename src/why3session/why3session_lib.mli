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

val read_session : string -> Session_itp.session * int option
(** [read_session s] reads the session file [s] and returns a pair
[(ses,shape_version)] where [ses] is the session structure (without
any tasks) and [shape_version] indicates the shapes version, if any *)

val read_update_session :
  allow_obsolete:bool -> Env.env ->
  Whyconf.config -> string ->
  Controller_itp.controller * bool * bool

(** {2 Spec for filtering } *)
type filter_prover

val read_opt_prover : string -> filter_prover
val prover_of_filter_prover : config -> filter_prover -> Why3.Whyconf.prover
val provers_of_filter_prover : config -> filter_prover -> Why3.Whyconf.Sprover.t

type filters

val filter_spec : spec_list

val read_filter_spec : Whyconf.config -> filters * bool

val theory_iter_proof_attempt_by_filter :
  Session_itp.session ->
  filters ->
  (Session_itp.proof_attempt_node -> unit) -> Session_itp.theory -> unit

val session_iter_proof_attempt_by_filter :
  Session_itp.session ->
  filters ->
  (Session_itp.proof_attempt_node -> unit) ->  unit


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

val get_used_provers : Session_itp.session -> Whyconf.Sprover.t
(** [get_used_provers s] returns the set of provers used somewhere in
    session [s] *)

val get_used_provers_file : Session_itp.session -> Session_itp.file
                              -> Whyconf.Sprover.t
(** [get_used_provers_file s f] returns the set of provers used
    somewhere in the file [f] of session [s] *)

val get_used_provers_theory : Session_itp.session -> Session_itp.theory
                              -> Whyconf.Sprover.t
(** [get_used_provers_theory s th] returns the set of provers used
    somewhere in the theory [th] of session [s] *)

val get_used_provers_goal : Session_itp.session -> Session_itp.proofNodeID
                            -> Whyconf.Sprover.t
(** [get_used_provers_goal s g] returns the set of provers used
    somewhere under the goal [g] of session [s] *)

val get_transf_string : Session_itp.session -> Session_itp.transID -> string
(** [get_transf_string s tr] concatenates the name of transformation [tr]
    in session [s] with its arguments *)

val goal_full_name : Session_itp.session ->  Session_itp.proofNodeID -> string
(** name of goal, taking account explanation *)

val goal_depth : Session_itp.session -> Session_itp.proofNodeID -> int
(** [goal_depth s g] returns the depth of the tree under goal
    [g] in session [s] *)

val theory_depth : Session_itp.session -> Session_itp.theory -> int
(** [theory_depth s th] returns the depth of the tree under theory
    [th] in session [s] *)

val file_depth : Session_itp.session -> Session_itp.file -> int
(** [file_depth s f] returns the depth of the tree under file [f] in
    session [s] *)
