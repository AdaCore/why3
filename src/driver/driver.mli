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
open Ident
open Task
open Trans
open Env

(** creating drivers *)

type raw_driver

val load_driver : string -> env -> raw_driver

(** cooked driver *)
type driver

val cook_driver : env -> clone -> Theory.use_map -> raw_driver -> driver

(** querying drivers *)

type translation =
  | Remove
  | Syntax of string
  | Tag of Util.Sstr.t

val query_ident : driver -> ident -> translation
val syntax_arguments : string -> (formatter -> 'a -> unit) -> 
  formatter -> 'a list -> unit
  (* syntax_argument templ print_arg fmt l print in the formatter fmt
     the list l using the template templ and the printer print_arg *)
  (** registering printers *)

type printer = driver -> formatter -> task -> unit

val register_printer : string -> printer -> unit

val register_transform   : string -> task Register.trans_reg -> unit
val register_transform_l : string -> task Register.tlist_reg  -> unit

val list_printers   : unit -> string list
val list_transforms : unit -> string list

(** using drivers *)

(** transform task *)
val apply_transforms : driver -> task -> task list

(** print_task *)
val print_task : printer

val filename_of_goal : driver -> string -> string -> task -> string
(* filename_of_goal filename theory_name ctxt *)

type prover_answer =
    Call_provers.prover_answer =
  | Valid
  | Invalid
  | Unknown of string
  | Failure of string
  | Timeout
  | HighFailure

val call_prover :
  ?debug:bool -> (* if on print on stderr the commandline
                    and the output of the prover *)
  ?timeout:int -> (* specify the time limit given to the prover,
                     if not set unlimited time *)
  driver ->       (* the driver to use *)
  task ->      (* the task to prove with a goal as the last declaration *)
  Call_provers.prover_result

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

(* error reporting *)

type error

exception Error of error

val report : formatter -> error -> unit
