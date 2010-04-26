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

(** Call provers and parse there outputs *)

type prover_answer =
  | Valid 
      (** The task is valid according to the prover *)
  | Invalid 
      (** The task is invalid *)
  | Timeout 
      (** the task timeout, ie it takes more time than specified*)
  | Unknown of string 
      (** The prover can't determined the validity or not of the task *)
  | Failure of string
      (** The prover report a failure *)
  | HighFailure 
      (** An error occured during the call to the prover or none of
      the given regexp match the output of the prover *)

type prover_result = {
  pr_answer : prover_answer;
  (* The answer of the prover on the given task*)
  pr_output : string;
  (* The output of the prover currently stderr and stdout *)
  pr_time   : float;
  (* The time taken by the prover *)
}

val print_prover_answer : Format.formatter -> prover_answer -> unit
(** Pretty-print a {! prover_answer} *)

val print_prover_result : Format.formatter -> prover_result -> unit
(** Pretty-print a prover_result. The answer and the time are output.
    The output of the prover is printed if and only if the answer is an 
    [HighFailure] *)

val call_on_buffer :
  ?debug    : bool ->
  command   : string ->
  timelimit : int ->
  memlimit  : int ->
  regexps   : (Str.regexp * prover_answer) list ->
  exitcodes : (int * prover_answer) list ->
  filename  : string ->
  Buffer.t ->
  unit -> prover_result
(** Call a prover on the task printed in the {!type: Buffer.t} given.
    @param debug : set the debug flag. 
    Print on stderr the commandline called and the output of the prover. *)
