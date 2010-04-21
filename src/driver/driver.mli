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

(** {2 create a driver} *)

type driver

val load_driver : env -> string -> driver
(** loads a driver from a file
    @param env TODO
    @param string driver file name
*)

(** {2 query a driver} *)

type translation =
  | Remove
  | Syntax of string
  | Tag of Util.Sstr.t

val syntax_arguments : string -> (formatter -> 'a -> unit) ->
  formatter -> 'a list -> unit
  (** (syntax_argument templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

(** {2 register printers and transformations} *)

type printer = (ident -> translation) -> formatter -> task -> unit

val register_printer : string -> printer -> unit

val register_transform   : string -> task Register.trans_reg -> unit
val register_transform_l : string -> task Register.tlist_reg -> unit

val list_printers   : unit -> string list
val list_transforms : unit -> string list

(** {2 use a driver} *)

val apply_transforms : driver -> task -> task list
(** transform task *)

val print_task : driver -> formatter -> task -> unit
(** print a task *)

val file_of_task : driver -> string -> string -> task -> string
(** file_of_task input_file theory_name task *)

val prove_task :
  ?debug    : bool ->
  command   : string ->
  timelimit : int ->
  memlimit  : int ->
  driver -> task -> unit -> Call_provers.prover_result

val call_on_buffer :
  ?debug    : bool ->
  command   : string ->
  timelimit : int ->
  memlimit  : int ->
  driver -> Buffer.t -> unit -> Call_provers.prover_result

(** {2 error reporting} *)

type error

exception Error of error

val report : formatter -> error -> unit

