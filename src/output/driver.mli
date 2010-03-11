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

(** using drivers *)

val print_context : printer

val filename_of_goal : driver -> Ident.ident_printer ->
  string -> string -> context -> string
(* filename_of_goal printer file_ident theory_ident ctxt *)

type prover_answer =
  | Valid
  | Invalid
  | Unknown of string
  | Failure of string
  | Timeout

val call_prover : driver -> context -> prover_answer
val call_prover_on_file : driver -> string -> prover_answer
val call_prover_on_channel : driver -> string -> in_channel -> prover_answer

(* error reporting *)

type error

exception Error of error

val report : formatter -> error -> unit
