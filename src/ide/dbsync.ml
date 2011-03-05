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
module Hprover = Db.Hprover

type transf_id = Db.transf_id
module Htransf = Db.Htransf

type file = Db.file
type theory = Db.theory
type goal = Db.goal
type proof_attempt = Db.proof_attempt
type transf = Db.transf
type proof_status = Db.proof_status

let m = Mutex.create ()

let mutex1 fn a1 = 
  Mutex.lock m;
  try let res = fn a1 in Mutex.unlock m; res
  with e -> Mutex.unlock m ; raise e

let mutex2 fn a1 a2 = 
  Mutex.lock m;
  try let res = fn a1 a2 in Mutex.unlock m; res
  with e -> Mutex.unlock m ; raise e

let mutex3 fn a1 a2 a3 = 
  Mutex.lock m;
  try let res = fn a1 a2 a3 in Mutex.unlock m; res
  with e -> Mutex.unlock m ; raise e

let prover_name pid = mutex1 Db.prover_name pid
let transf_name tid = mutex1 Db.transf_name tid
let status_and_time pa = mutex1 Db.status_and_time pa
let edited_as pa = mutex1 Db.edited_as pa
let goal_name g = mutex1 Db.goal_name g
let task_checksum g = mutex1 Db.task_checksum g
let external_proofs g = mutex1 Db.external_proofs g
let transformations g = mutex1 Db.transformations g
let subgoals tr = mutex1 Db.subgoals tr
let theory_name th = mutex1 Db.theory_name th
let goals th = mutex1 Db.goals th
let theories f = mutex1 Db.theories f
let init_base s = mutex1 Db.init_base s
let is_initialized u = mutex1 Db.is_initialized u
let db_name u = mutex1 Db.db_name u
let files u = mutex1 Db.files u

exception AlreadyExist

let prover_from_name s = mutex1 Db.prover_from_name s
let transf_from_name s = mutex1 Db.transf_from_name s
let add_proof_attempt g pid = mutex2 Db.add_proof_attempt g pid
let remove_proof_attempt pa = mutex1 Db.remove_proof_attempt pa
let set_obsolete pa = mutex1 Db.set_obsolete pa
let set_status pa ps t = mutex3 Db.set_status pa ps t
let set_edited_as pa s = mutex2 Db.set_edited_as pa s

let add_transformation g tid = mutex2 Db.add_transformation g tid
let remove_transformation tr = mutex1 Db.remove_transformation tr

let add_goal th s1 s2 = mutex3 Db.add_goal th s1 s2
let change_checksum g s = mutex2 Db.change_checksum g s
let add_subgoal tr s1 s2 = mutex3 Db.add_subgoal tr s1 s2

let add_theory f s = mutex2 Db.add_theory f s
let add_file s = mutex1 Db.add_file s

