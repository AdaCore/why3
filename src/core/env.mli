(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Environments} *)

open Wstdlib

(** Local type aliases *)

type fformat = string (* format name *)
type filename = string (* file name *)
type extension = string (* file extension *)
type pathname = string list (* library path *)

(** Library environment *)

type env

val env_tag : env -> Weakhtbl.tag

module Wenv : Weakhtbl.S with type key = env

val create_env : filename list -> env
(** creates an environment from a "loadpath", a list of directories
    containing loadable Why3/WhyML/etc files *)

val get_loadpath : env -> filename list
(** returns the loadpath of a given environment *)

(** {2 Input languages} *)

type 'a language

val base_language : Theory.theory Mstr.t language
(** [base_language] is the root of the tree of supported languages.
    Any input language must be translatable into pure theories for
    the purposes of verification. *)

val register_language : 'a language -> ('b -> 'a) -> 'b language
(** [register_language parent convert] adds a leaf to the language tree.
    The [convert] function provides translation from the new language to
    [parent]. *)

val add_builtin : 'a language -> (pathname -> 'a) -> unit
(** [add_builtin lang builtin] adds new builtin libraries to [lang].
    The [builtin] function is called by [read_library] (below) for any
    library path that starts with "why3" (this prefix is not passed to
    [builtin]). For all library paths not covered by [builtin] it must
    raise [Not_found].

    By convention, every builtin theory of the base language is placed
    under a separate pathname that ends with the name of the theory.
    For example, the full qualified name of the [Builtin] theory is
    [why3.Builtin.Builtin]. The name of the theory is duplicated in
    the library path to ensure that every builtin theory is obtained
    from a separate call to [builtin], which permits to generate
    builtin theories on demand.

    If there are several definitions of a builtin library for a given
    language and path, they must be physically identical, otherwise
    [LibraryConflict] is raised. For example, if an offspring language
    provides extended definitions of builtin theories, they must be
    [convert]'ed into exactly the same singleton [theory Mstr.t] maps
    as stored for the base language. *)

val base_language_builtin : pathname -> Theory.theory Mstr.t
(** [base_language_builtin path] returns the builtin theories defined
    by the base language. Any offspring language that provides extended
    definitions of builtin theories must use these as the result of
    the conversion function. *)

type 'a format_parser = env -> pathname -> filename -> in_channel -> 'a
(** [(fn : 'a format_parser) env path file ch] parses the in_channel [ch]
    and returns the language-specific contents of type ['a]. References
    to libraries in the input file are resolved via [env]. If the parsed
    file is itself a library file, the argument [path] contains the fully
    qualified library path of the file, which can be put in the identifiers.
    The string argument [file] indicates the origin of the stream (file name)
    to be used in error messages. *)

exception KnownFormat of fformat

val register_format :
  desc:Pp.formatted ->
  'a language -> fformat -> extension list -> 'a format_parser -> unit
(** [register_format ~desc lang fname exts parser] registers a new format
    [fname] for files with extensions from the string list [exts] (without
    the separating dot). Any previous associations of extensions from [exts]
    to other formats are overridden.

    @raise KnownFormat [name] if the format is already registered *)

val list_formats :
  'a language -> (fformat * extension list * Pp.formatted) list
(** [list_formats lang] returns the list of registered formats that can
    be translated to [lang]. Use [list_formats base_language] to obtain
    the list of all registered formats. *)

(** {2 Language-specific parsers} *)

exception InvalidFormat of fformat
exception UnknownFormat of fformat
exception UnknownExtension of extension
exception UnspecifiedFormat

val read_channel :
  ?format:fformat -> 'a language -> env -> filename -> in_channel -> 'a
(** [read_channel ?format lang env file ch] returns the contents of [ch]
    in language [lang]. When given, [format] enforces the format, otherwise
    we choose the parser according to [file]'s extension. Nothing ensures
    that [ch] corresponds to the contents of [file].

    @raise InvalidFormat [format] if the format, given in the parameter
      or determined from the file's extension, does not translate to [lang]
    @raise UnknownFormat [format] if the format is not registered
    @raise UnknownExtension [s] if the extension [s] is not known
      to any registered parser
    @raise UnspecifiedFormat if format is not given and [file]
      has no extension *)

val read_file : ?format:fformat -> 'a language -> env -> filename -> 'a
(** an open-close wrapper around [read_channel] *)

exception LibraryNotFound of pathname
exception LibraryConflict of pathname
exception AmbiguousPath of filename * filename

val read_library : 'a language -> env -> pathname -> 'a
(** [read_library lang env path] returns the contents of the library
    file specified by [path]. If [path] starts with ["why3"] then the
    [builtin] functions of the language are called on [List.tl path].
    If [path] is empty, [builtin] are called on the empty path.

    @raise InvalidFormat [format] if the format of the library file,
      determined from the file's extension, does not translate to [lang]
    @raise LibraryNotFound [path] if the library file was not found
    @raise LibraryConflict [path] if a bultin library has several
      non-physically-equal definitions
    @raise AmbiguousPath [(file1,file2)] if [env] contains two library
      files corresponding to [path] *)

val locate_library : env -> pathname -> filename
(** [locate_library env path] returns the location of the library
    file specified by [path].

    This is a low-level function that allows to access a library file
    without parsing it. Do not use it without a good reason.

    @raise LibraryNotFound [path] if the library file was not found
    @raise AmbiguousPath [(file1,file2)] if [env] contains two library
      files corresponding to [path]
    @raise InvalidArgument if the library path starts with "why3" or
      is empty. *)

exception TheoryNotFound of pathname * string

val read_theory : env -> pathname -> string -> Theory.theory
(** [read_theory env path th] returns the theory [path.th] from
    the library. If [path] is empty, it is assumed to be ["why3".th],
    that is, [read_theory env [] "Bool"] will look for the builtin
    theory [why3.Bool.Bool] (see [register_language]).

    @raise LibraryNotFound [path] if the library file was not found
    @raise LibraryConflict [path] if a bultin library has several
      non-physically-equal definitions
    @raise AmbiguousPath [(file1,file2)] if [env] contains two library
      files corresponding to [path]
    @raise TheoryNotFound if the theory was not found in the file *)
