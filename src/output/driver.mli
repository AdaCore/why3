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

val load_driver : string -> Typing.env -> driver

(** querying drivers *)

type translation = 
  | Remove
  | Syntax of string
  | Tag of Snm.t

val query_ident : driver -> ident -> translation

(** registering printers *)

type printer = driver -> formatter -> context -> unit

val register_printer : string -> printer -> unit

(** using drivers *)

val print_context : printer

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
