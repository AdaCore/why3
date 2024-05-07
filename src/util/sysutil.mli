(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* create a backup copy of a file if it exists *)
val backup_file : string -> unit

(* return the content of an in-channel *)
val channel_contents : in_channel -> string

(* return the content of an in_channel in a buffer *)
val channel_contents_buf : in_channel -> Buffer.t

(* put the content of an in_channel in a formatter *)
val channel_contents_fmt : in_channel -> Format.formatter -> unit

(* fold on the line of a file *)
val fold_channel : ('a -> string -> 'a) -> 'a -> in_channel -> 'a

(* return the content of a file *)
val file_contents : string -> string

(* return the content of a file in a buffer *)
val file_contents_buf : string -> Buffer.t

(* put the content of a file in a formatter *)
val file_contents_fmt : string -> Format.formatter -> unit

(* [write_file f c] writes the content [c] into the file [f] *)
val write_file : string -> string -> unit

(* [write_file_fmt f c] writes the content given to the formatter [c] into the
   file [f] *)
val write_file_fmt : string -> (Format.formatter -> unit) -> unit

(* [write_unique_file_fmt f c] writes the content given to the formatter [c]
   into the uniquified file [f]. The uniquification is not specified except
   it keeps the extension.  *)
val write_unique_file_fmt : string -> (Format.formatter -> unit) -> unit

val open_temp_file :
  ?debug:bool -> (* don't remove the file *)
  string -> (string -> out_channel -> 'a) -> 'a
(* open_temp_file suffix usefile
   Create a temporary file with suffix suffix,
   and call usefile on this file (filename and open_out).
   usefile can close the file *)

val copy_file : string -> string -> unit
(** [copy_file from to] copy the file from [from] to [to] *)

val copy_dir : string -> string -> unit
(** [copy_dir from to] copy the directory recursively from [from] to [to],
    currently the directory must contains only directories and common files
*)

val concat : string -> string -> string
(** like [Filename.concat] but returns only second string when it is already absolute *)

type file_path
val empty_path : file_path
val add_to_path : file_path -> string -> file_path
val is_empty_path : file_path -> bool
val decompose_path : file_path -> string list
val basename : file_path -> string

val print_file_path : Format.formatter -> file_path -> unit

val system_independent_path_of_file : string -> file_path
(** [system_independent_path_of_file filename] return the access path
    of [filename], in a system-independent way *)

val system_dependent_absolute_path : string -> file_path -> string
(** [system_dependent_absolute_path d p] returns the
    system-dependent absolute path for the abstract path [p] relative
    to directory [d] *)

val relativize_filename : string -> string -> file_path
(** [relativize_filename base filename] returns an access path for
    filename [filename] relatively to [base]. The [filename] is split
    into path components using the system-dependent calls to
    [Filename.dirname] and [Filename.basename].

    OBSOLETE COMMENT? [base] should not contain occurrences of "." and "..",
    which can be removed by calling first [normalize_filename].

    FIXME: this function does not handle symbolic links properly
 *)


val uniquify : string -> string
(** find filename that doesn't exist based on the given filename.
    Be careful the file can be taken after the return of this function.
*)


exception AmbiguousResolve of string list
exception FailedResolve of string list

val resolve_from_paths : string list -> string -> string
(** [resolve_from_paths \[p1;..;pn\] name] search for an existing
   file among [p1/name],..,[pn/name]. Raises [FailedResolve] if no
   such file is found, with the set of tried file names as
   argument. Raise [AmbiguousResolve] if several exist, with the set
   of resolved names as argument.

  If [name] is already an absolute file name, this function returns
   [name] if the file exists, raises [FailedResolve] otherwise, with
   name as argument.

 *)

val deep_mkdir: string -> unit
(** Ensure the existence of directories all along the given `path`. If a
    directory does not exist, it is created with permission 755.
    @raise Sys_error if a part of the path exists but is not a directory
 *)
