(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Why

type prover_id = Db.prover_id
type transf_id = Db.transf_id 

type file = Db.file
type theory = Db.theory
type goal = Db.goal
type proof_attempt = Db.proof_attempt
type transf = Db.transf
type proof_status = Db.proof_status

val prover_name : prover_id -> string
val transf_name : transf_id -> string
val status_and_time : proof_attempt -> proof_status * float * bool * string
val edited_as : proof_attempt -> string
val goal_name : goal -> string
val task_checksum : goal -> string (** checksum *)
val external_proofs: goal -> proof_attempt Db.Hprover.t
val transformations : goal -> transf Db.Htransf.t
val subgoals : transf -> goal Util.Mstr.t
val theory_name : theory -> string
val goals : theory -> goal Util.Mstr.t
val theories : file -> theory Util.Mstr.t
val init_base : string -> unit
val is_initialized : unit -> bool
val db_name : unit -> string
val files : unit -> (file * string) list

exception AlreadyExist

val prover_from_name : string -> prover_id
val transf_from_name : string -> transf_id
val add_proof_attempt : goal -> prover_id -> proof_attempt
val remove_proof_attempt : proof_attempt -> unit
val set_obsolete : proof_attempt -> unit
val set_status : proof_attempt -> proof_status -> float -> unit
val set_edited_as : proof_attempt -> string -> unit

val add_transformation : goal -> transf_id -> transf
val remove_transformation : transf -> unit 

val add_goal : theory -> string -> string -> goal
val change_checksum: goal -> string -> unit
val add_subgoal : transf -> string -> string -> goal

val add_theory : file -> string -> theory
val add_file :  string -> file
