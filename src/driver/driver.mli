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

(** Drivers for calling external provers *)

open Format
open Ident
open Task
open Trans
open Env

(** {2 creating drivers} *)

type driver


val load_driver : string -> env -> driver
(** loads a driver from a file
    @param string driver file name 
    @param env TODO
*)

(** {2 querying drivers} *)

type translation =
  | Remove
  | Syntax of string
  | Tag of Util.Sstr.t

val syntax_arguments : string -> (formatter -> 'a -> unit) -> 
  formatter -> 'a list -> unit
  (** (syntax_argument templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)


(** {2 registering printers} *)

type printer = (ident -> translation) -> formatter -> task -> unit

val register_printer : string -> printer -> unit

val register_transform   : string -> task Register.trans_reg -> unit
val register_transform_l : string -> task Register.tlist_reg  -> unit

val list_printers   : unit -> string list
val list_transforms : unit -> string list

(** {2 using drivers} *)

val apply_transforms : driver -> task -> task list
(** transform task *)

val print_task : driver -> formatter -> task -> unit
(** print a task *)

val filename_of_goal : driver -> string -> string -> task -> string
(** filename_of_goal filename theory_name ctxt *)

type prover_answer = Call_provers.prover_answer =
  | Valid
  | Invalid
  | Unknown of string
  | Failure of string
  | Timeout
  | HighFailure

val call_prover : ?debug:bool -> ?timeout:int -> driver -> task -> 
  Call_provers.prover_result
(** calls a prover on a given task
    @param debug if on, prints on stderr the command line 
                 and the output of the prover 
    @param timeout specifies the CPU time limit given to the prover,
                     if not set: unlimited time
    @param driver the driver to use
    @param task the task to prove with a goal as the last declaration
    @return the prover's answer
  *)

val call_prover_ext : ?debug:bool -> ?timeout:int -> driver -> task -> 
  (unit -> Call_provers.prover_result)
(** same as {!Driver.call_prover} but split the function between 
    thread unsafe and thread safe operation.
    call_prover_ext ~debug ~timeout driver task prepares the goal 
    and return a function which actually call the prover on the goal.
    The returned function is thread safe.
  *)

val call_prover_on_file :
  ?debug:bool ->
  ?timeout:int ->
  driver ->
  string ->
    Call_provers.prover_result

val call_prover_on_formatter :
  ?debug:bool ->
  ?timeout:int ->
  ?filename:string ->
  driver ->
  (formatter -> unit) ->
  Call_provers.prover_result

(** {2 error reporting} *)

type error

exception Error of error

val report : formatter -> error -> unit
