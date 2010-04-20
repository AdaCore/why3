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

type prover_answer =
  | Valid
  | Invalid
  | Timeout
  | Unknown of string
  | Failure of string
  | HighFailure

type prover_result = {
  pr_answer : prover_answer;
  pr_output : string;
  pr_time   : float;
}

type prover_regexp = Str.regexp * prover_answer

val print_prover_answer : Format.formatter -> prover_answer -> unit
val print_prover_result : Format.formatter -> prover_result -> unit

val call_on_buffer :
  ?debug : bool ->
  ?suffix : string ->
  command : string ->
  timelimit : int ->
  memlimit : int ->
  regexps : prover_regexp list ->
  Buffer.t ->
  (unit -> prover_result)

val call_on_formatter :
  ?debug : bool ->
  ?suffix : string ->
  command : string ->
  timelimit : int ->
  memlimit : int ->
  regexps : prover_regexp list ->
  (Format.formatter -> unit) ->
  (unit -> prover_result)

val call_on_file :
  ?debug : bool ->
  ?suffix : string ->
  command : string ->
  timelimit : int ->
  memlimit : int ->
  regexps : prover_regexp list ->
  string ->
  (unit -> prover_result)

