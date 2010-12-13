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

(** Access to Environment, Load Path *)

open Theory

type env

val env_tag : env -> Hashweak.tag

module Wenv : Hashweak.S with type key = env

type retrieve_channel = string list -> string * in_channel
  (** retrieves a channel from a given path; a filename is also returned, 
      for printing purposes only *)

type retrieve_theory  = env -> string list -> theory Mnm.t

val create_env : retrieve_channel -> retrieve_theory -> env

exception TheoryNotFound of string list * string

val find_theory : env -> string list -> string -> theory
  (** [find_theory e p n] finds the theory named [p.n] in environment [e]
      @raise TheoryNotFound if theory not present in env [e] *)

val find_channel : env -> string list -> string * in_channel

(** Parsers *)

type read_channel = env -> string -> in_channel -> theory Mnm.t
  (** a function of type [read_channel] parses the given channel using
      its own syntax. The string argument indicates the origin of the stream
      (e.g. file name) to be used in error messages *)

val register_format : string -> string list -> read_channel -> unit
  (** [register_format name extensions f] registers a new format
      under name [name], for files with extensions in list [extensions];
      [f] is the function to perform parsing *)

exception NoFormat
exception UnknownExtension of string
exception UnknownFormat of string (* format name *)

val read_channel : ?format:string -> read_channel
(** [read_channel ?format env f c] returns the map of theories
    in channel [c]. When given, [format] enforces the format, otherwise
    the format is chosen according to [f]'s extension.
    Beware that nothing ensures that [c] corresponds to the contents of [f]

    @raise NoFormat if [format] is not given and [f] has no extension
    @raise UnknownExtension [s] if the extension [s] is not known in
      any registered parser
    @raise UnknownFormat [f] if the [format] is not registered
*)

val read_file : ?format:string -> env -> string -> theory Mnm.t
(** [read_file ?format env f] returns the map of theories
    in file [f]. When given, [format] enforces the format, otherwise
    the format is chosen according to [f]'s extension. *)

val list_formats : unit -> (string * string list) list

