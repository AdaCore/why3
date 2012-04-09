(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Util
open Theory

(** Local type aliases and exceptions *)

type fformat = string (* format name *)
type filename = string (* file name *)
type extension = string (* file extension *)
type pathname = string list (* library path *)

exception KnownFormat of fformat
exception UnknownFormat of fformat
exception UnknownExtension of extension
exception UnspecifiedFormat
exception LibFileNotFound of pathname
exception TheoryNotFound of pathname * string

(** Library environment *)

type env

val env_tag : env -> Hashweak.tag

module Wenv : Hashweak.S with type key = env

val create_env : filename list -> env
(** creates an environment from a "loadpath", a list of directories
    containing loadable Why3/WhyML/etc files *)

val get_loadpath : env -> filename list
(** returns the loadpath of a given environment *)

val read_channel :
  ?format:fformat -> env -> filename -> in_channel -> theory Mstr.t
(** [read_channel ?format env path file ch] returns the theories in [ch].
    When given, [format] enforces the format, otherwise we choose
    the format according to [file]'s extension. Nothing ensures
    that [ch] corresponds to the contents of [file].

    @raise UnknownFormat [format] if the format is not registered
    @raise UnknownExtension [s] if the extension [s] is not known
      to any registered parser
    @raise UnspecifiedFormat if format is not given and [file]
      has no extension *)

val read_file : ?format:fformat -> env -> filename -> theory Mstr.t
(** [read_file ?format env file] returns the theories in [file].
    When given, [format] enforces the format, otherwise we choose
    the format according to [file]'s extension. *)

val read_theory : format:fformat -> env -> pathname -> string -> theory
(** [read_theory ~format env path th] returns the theory [path.th]
    from the library. The parameter [format] speicifies the format
    of the library file to look for.

    @raise UnknownFormat [format] if the format is not registered
    @raise LibFileNotFound [path] if the library file was not found
    @raise TheoryNotFound if the theory was not found in the file *)

val find_theory : env -> pathname -> string -> theory
(** the same as [read_theory ~format:"why"]

    This function is left for compatibility purposes and may be
    removed in future versions of Why3. *)

(** Input formats *)

type 'a library
(** part of the environment restricted to a particular format *)

type 'a read_format =
  'a library -> pathname -> filename -> in_channel -> 'a * theory Mstr.t
(** [(fn : 'a read_format) lib path file ch] parses the channel [ch]
    and returns the format-specific contents of type ['a] and a set of
    logical theories. References to the library files of the same format
    are resolved via [lib]. If the parsed file is itself a part of
    the library, the argument [path] contains the fully qualified
    library name of the file, which can be put in the identifiers.
    The string argument [file] indicates the origin of the stream
    (e.g. file name) to be used in error messages. *)

val register_format :
  fformat -> extension list -> 'a read_format -> (env -> 'a library)
(** [register_format fname exts read] registers a new format [fname]
    for files with extensions from the string list [exts] (without
    the separating dot); [read] is the function to perform parsing.
    Returns a function that maps an environment to a format-specific
    library inside it.

    @raise KnownFormat [name] if the format is already registered *)

val env_of_library : 'a library -> env
(** [env_of_library lib] returns the environment of [lib] *)

val list_formats : unit -> (fformat * extension list) list
(** [list_formats ()] returns the list of registered formats *)

val read_lib_file : 'a library -> pathname -> 'a * theory Mstr.t
(** [read_lib_file lib path] retrieves the contents of a library file

    @raise LibFileNotFound [path] if the library file was not found *)

val read_lib_theory : 'a library -> pathname -> string -> theory
(** [read_lib_theory lib path th] returns the theory [path.th]
    from the library. This is the same as [read_theory] above,
    but the format is determined by [lib] and not by the extra
    [format] parameter.

    @raise LibFileNotFound [path] if the library file was not found
    @raise TheoryNotFound if the theory was not found in the file *)

val locate_lib_file : env -> fformat -> pathname -> filename
(** [locate_lib_file env format path] finds a library file in a given
    environment, knowing its format and its library path

    This is a low-level function that allows to accees a library file
    without parsing it. Do not use it without a good reason to do.

    @raise LibFileNotFound [path] if the library file was not found
    @raise UnknownFormat [format] if the format is not registered *)

