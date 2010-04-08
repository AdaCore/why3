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

open Format

type prover_answer = 
  | Valid
  | Invalid
  | Unknown of string  
  | Failure of string        
  | Timeout
  | HighFailure

val print_prover_answer : formatter -> prover_answer -> unit

type prover_result =
    { pr_time   : float;
      pr_answer : prover_answer;
      pr_stderr : string;
      pr_stdout : string}

val print_prover_result : formatter -> prover_result -> unit

type prover =
    { pr_call_stdin : string option; (* %f pour le nom du fichier *)
      pr_call_file  : string option;
      pr_regexps    : (Str.regexp * prover_answer) list; 
      (* \1,... sont remplacés *)
    }

exception CommandError
exception NoCommandlineProvided      

val cpulimit : string ref

val on_file : 
  ?debug:bool -> 
  ?timeout:int -> 
  prover -> 
  string -> 
  prover_result

val on_formatter : 
  ?debug:bool ->
  ?timeout:int -> 
  ?filename:string -> (* used as the suffix of a tempfile if the prover can't 
                         deal with stdin *)
  prover -> 
  (formatter -> unit) -> 
  prover_result

val on_buffer : 
  ?debug:bool ->
  ?timeout:int -> 
  ?filename:string -> (* used as the suffix of a tempfile if the prover can't 
                         deal with stdin *)
  prover -> 
  Buffer.t -> 
  prover_result
