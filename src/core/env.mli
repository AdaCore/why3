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

open Theory

(** Environment *)

type env

type retrieve_theory = env -> string list -> theory Mnm.t

val create_env : retrieve_theory -> env

(** ??? *)
val find_theory : env -> string list -> string -> theory

val env_tag : env -> int

exception TheoryNotFound of string list * string


(** Parsers *)

type parse_only   = env -> string -> in_channel -> unit
type read_channel = env -> string -> in_channel -> theory Mnm.t
type error_report = Format.formatter -> exn -> unit

val register_parser :
  string -> string list -> parse_only -> read_channel -> error_report -> unit
  (** [register_parser name extensions f1 f2] registers a new parser
      under name [name], for files with extensions in list [extensions];
      [f1] is the function to perform parsing only;
      [f2] is the function to retrieve a list of theories from a channel *)

val parse_only   : ?name:string -> parse_only

val read_channel : ?name:string -> read_channel

val report : ?name:string -> string -> error_report

exception UnknownParser of string (* parser name *)

val list_formats : unit -> (string * string list) list

