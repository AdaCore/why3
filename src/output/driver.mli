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
open Theory

(** creating drivers *)

type driver 

val load_driver : string -> env -> driver

(** querying drivers *)

type translation = 
  | Remove
  | Syntax of string
  | Tag of Snm.t

val query_ident : driver -> ident -> translation
val syntax_arguments : string -> (formatter -> 'a -> unit) -> formatter -> 'a list -> unit
  (* syntax_argument templ print_arg fmt l print in the formatter fmt
     the list l using the template templ and the printer print_arg *)
  (** registering printers *)

type printer = driver -> formatter -> context -> unit

val register_printer : string -> printer -> unit

val register_transform : string -> (unit -> Transform.ctxt_t) -> unit

val list_printers : unit -> string list
val list_transforms : unit -> string list

(** using drivers *)

(** transform context *)
val apply_before_split : driver -> context -> context
val apply_after_split : driver -> context -> context

(** print_context *)
val print_context : printer

val filename_of_goal : driver -> Ident.ident_printer ->
  string -> string -> context -> string
(* filename_of_goal printer file_ident theory_ident ctxt *)

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
  context ->      (* the context to prove with a goal as the last declaration *)
  Call_provers.prover_result

val call_prover_on_file : 
  ?debug:bool -> 
  ?timeout:int -> 
  driver -> 
  string -> 
    Call_provers.prover_result

val call_prover_on_buffer : 
  ?debug:bool -> 
  ?timeout:int -> 
  ?filename:string -> 
  driver -> 
  Buffer.t -> 
  Call_provers.prover_result

(* error reporting *)

type error

exception Error of error

val report : formatter -> error -> unit
