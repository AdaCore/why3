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

(** This module is a wrapper around Session which is simpler when you
    only want to read a session *)

open Why3
open Util

type session = file list

and file = private
    { file_name : string;
      theories  : theory list;
      file_verified : bool}

and theory = private
    { theory_name : string;
      theory : Theory.theory;
      goals : goal list;
      theory_verified : bool}

and goal = private
    { goal_name : string;
      goal_expl : string;
      goal_verified : bool;
      transformations : transf Mstr.t;
      external_proofs : proof_attempt Mstr.t}

and transf = private
    { transf_name : string;
      transf_verified : bool;
      subgoals : goal list}

and prover_data = private
    { prover_name : string;
      prover_version : string;
      prover_interactive : bool;
    }

and prover_option = private
  | Detected_prover of prover_data
  | Undetected_prover of string


and proof_attempt_status = private
  | Undone
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)

and proof_attempt = private
  { prover : prover_option;
    proof_state : proof_attempt_status;
    timelimit : int;
    proof_obsolete : bool;
    edited_as : string option;
  }
    (** a proof attempt for a given goal *)

type env =
  { env : Env.env;
    config : Whyconf.config}

val read_config : ?includes:string list -> string option -> env
(** [read_config ~includes conf_path] read the configuration located in
    [conf_path] or use the default location if [conf_path] is [None].
    Add the directory in [includes] in the loadpath  *)

val read_project_dir :
  allow_obsolete:bool ->
  env:env -> string -> session
(** read the session which is in the given directory;
    return {Notfound} if the directory doesn't exists
*)

val get_project_dir : string -> string
(** find the session which correspond to the given file or return
    directly the given directory;
    return {Not_found} if the file or the directory doesn't exists
*)
