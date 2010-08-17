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

val env_weak : env -> Hashweak.key

type retrieve_theory = env -> string list -> theory Mnm.t

val create_env : retrieve_theory -> env

exception TheoryNotFound of string list * string

val find_theory : env -> string list -> string -> theory
  (** [find_theory e p n] finds the theory named [p.n] in environment [e]
      @raises [TheoryNotFound p n] if theory not present in env [e] *)

(** Parsers *)

type read_channel =
  ?debug:bool -> ?parse_only:bool -> ?type_only:bool ->
  env -> string -> in_channel -> theory Mnm.t

type error_report = Format.formatter -> exn -> unit

val register_format :
  string -> string list -> read_channel -> error_report -> unit
  (** [register_format name extensions f1 f2] registers a new format
      under name [name], for files with extensions in list [extensions];
      [f1] is the function to perform parsing;
      [f2] is the function to report errors *)

val read_channel : ?name:string -> read_channel

val report : ?name:string -> string -> error_report

exception UnknownFormat of string (* format name *)

val list_formats : unit -> (string * string list) list

