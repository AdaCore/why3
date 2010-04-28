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

(** Manage Why drivers *)

open Format
open Util
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

type driver_query

val driver_query : driver -> task -> driver_query

val query_syntax : driver_query -> ident -> string option
val query_remove : driver_query -> ident -> bool
val query_tags   : driver_query -> ident -> Sstr.t
val query_clone  : driver_query -> Theory.clone_map
val query_driver : driver_query -> driver
val query_env    : driver_query -> env
val query_tag    : driver_query -> int

val print_global_prelude : driver_query -> formatter -> unit
val print_theory_prelude : driver_query -> ident -> formatter -> unit
val print_full_prelude   : driver_query -> task -> formatter -> unit

(** {2 use a driver} *)

val get_env : driver -> env
val get_printer : driver -> string option
val get_transform : driver -> string list

(** file_of_task input_file theory_name task *)
val file_of_task : driver -> string -> string -> task -> string

val call_on_buffer :
  ?debug    : bool ->
  command   : string ->
  ?timelimit : int ->
  ?memlimit  : int ->
  driver -> Buffer.t -> unit -> Call_provers.prover_result

(** {2 syntax arguments} *)

val syntax_arguments : string -> (formatter -> 'a -> unit) ->
  formatter -> 'a list -> unit
  (** (syntax_argument templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

(** {2 error reporting} *)

type error

exception Error of error

val report : formatter -> error -> unit

