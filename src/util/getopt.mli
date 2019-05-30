(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

Short keys represent [-l] options. Long keys represent [--long] options.
Some options can support both formats at once, e.g., [-l] and [--long].

For long-key options, if the handler is [Hnd1], an argument has to be passed
as [--long=value]. If the handler is [HndOpt], it can be passed either as
[--long] or [--long=value]. If the handler is [Hnd0], it has to be passed
as [--long].

For short-key options, if the handler is [Hnd1], an argument can be passed
either as [-lvalue] or [-l value]. If the handler is [HndOpt], it can be
passed either as [-l] or [-lvalue]. If the handler is [Hnd0], it has be
passed as [-l].

Short-key options with [Hnd0] or [HndOpt] handlers can be passed in
concatenated form, i.e., [-abc] is parsed as [-a -b -c], assuming the first
argument has a [Hnd0] handler.

If [--] is passed, all remaining arguments are considered as raw arguments.

*)

type key =
  | KShort of char
  | KLong of string
  | Key of char * string

type _ arg =
  | AInt : int arg
  | AString : string arg
  | ASymbol : string list -> string arg

type handler =
  | Hnd0 of (unit -> unit)
  | HndOpt : 'a arg * ('a option -> unit) -> handler
  | Hnd1 : 'a arg * ('a -> unit) -> handler

type doc = string

type opt = key * handler * doc

exception GetoptFailure of string

val parse_one : ?mm:bool -> opt list -> (string -> unit) -> string array -> int ref -> unit
(** [parse_one ~mm opts extra args i] parses argument [args.(!i)] using
    the option list [opts]. If the argument is not an option, it is passed
    to [extra]. Index [i] is made to point to the next argument to be
    parsed. When [mm] is true (default), the special argument [--] is
    recognized and causes all the remaining arguments to be passed to
    [extra]. The function raises [GetoptFailure] if the argument is either
    an unrecognized option or its required value is missing. If the option
    list is static, [parse_all] might be a better choice. *)

val parse_all : opt list -> (string -> unit) -> string array -> unit
(** [parse_all opts extra args] parses all the arguments, starting from
    [args.(1)], calling [parse_one] in turn. When [GetoptFailure] is raised,
    the function calls [handle_exn] to terminate the program. *)

val format : ?margin:int -> opt list -> string
(** [format ~margin opts] turns the option list [opts] into a string that
    is suitable for usage message. The first word of a description name the
    argument of the option (if any). Description remainders are aligned
    at column [margin] (25 by default). If an option does not support
    arguments, its description string should start with a space. *)

val handle_exn : string array -> exn -> unit
(** [handle_exn args exn] terminates the program after printing the content
    of the [GetoptFailure] exception. [args.(0)] is used as the program name
    for the error message. *)
