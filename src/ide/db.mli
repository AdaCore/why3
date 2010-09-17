(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

(** Proof database *)

(** {1 data types} *)

(** prover info *)
type prover

val prover_from_id : string -> prover

(** status of an external proof attempt *)
type proof_status =
  | Success (** external proof attempt succeeded *)
  | Timeout (** external proof attempt was interrupted *)
  | Unknown (** external prover answered ``don't know'' or equivalent *)
  | Failure (** external prover call failed *)

type proof_attempt 
type goal
type transf
type theory
type file
type goal_parent =
  | Theory of theory
  | Transf of transf

(** proof_attempt accessors *)
val prover : proof_attempt -> prover
val proof_goal : proof_attempt -> goal
val status : proof_attempt -> proof_status
val proof_obsolete : proof_attempt -> bool
val time : proof_attempt -> float
val edited_as : proof_attempt -> string


(** goal accessors *)
val parent : goal -> goal_parent
val task : goal -> string (* checksum *)
val proved : goal -> bool
val external_proofs: (string, proof_attempt) Hashtbl.t
val transformations : (string, transf) Hashtbl.t

(** transf accessors *)
val parent_goal : transf -> goal
val transf_name : transf -> string
val subgoals : transf -> goal list

(** theory accessors *)        
val theory_name : theory -> string
val goals : theory -> goal list
val verified : theory -> bool

(** file accessors *)
val file_name : file -> string
val theories : file -> theory list

(** {1 The persistent database} *)

val init_base : string -> unit
(** opens or creates the current database, from given file name *)

val files : unit -> file list
(** returns the current set of files *)



(** {1 Updates} *)


  
