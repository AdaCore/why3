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

val path_of_file : string -> string list
(** [path_of_file filename] return the absolute path of [filename] *)

(* unused ?
val normalize_filename : string -> string
 *)
(** [normalize_filename filename] removes from [filename] occurrences of
    "." and ".." that denote respectively the current directory and
    parent directory, whenever possible *)

val relativize_filename : string -> string -> string
(** [relativize_filename base filename] relativize the filename
    [filename] according to [base]. [base] should not contain occurrences of
    "." and "..", which can be removed by calling first [normalize_filename].
*)

val absolutize_filename : string -> string -> string
(** [absolutize_filename base filename] absolutize the filename
    [filename] according to [base] *)

val uniquify : string -> string
(** find filename that doesn't exists based on the given filename.
    Be careful the file can be taken after the return of this function.
*)
