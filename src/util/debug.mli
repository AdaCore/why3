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


type flag

(** Flags used for debugging only part of Why3 *)

val register_flag : desc:Pp.formatted -> string -> flag
(** Register a new flag. It is allowed to register twice the same flag *)

val register_stop_flag : desc:Pp.formatted -> string -> flag
(** Register a new stop flag. It is allowed to register twice the same flag.
    A stop flag should be used when the flag changes the behavior of Why3.
    Such flags are not set by --debug-all. *)

val lookup_flag : string -> flag
val list_flags : unit -> (string * flag * bool * Pp.formatted) list
(** List the known flags *)

val is_stop_flag : string -> bool
(** test if the flag is a stop flag *)

val flag_desc : string -> Pp.formatted
(** get the description of the flag *)

(** Modify the state of a flag *)
val set_flag : flag -> unit
val unset_flag : flag -> unit
val toggle_flag : flag -> unit

val test_flag : flag -> bool
(** Return the state of the flag *)
val nottest_flag : flag -> bool

val set_debug_formatter : Format.formatter -> unit
(** Set the formatter used when printing debug material *)

val get_debug_formatter : unit -> Format.formatter
(** Get the formatter used when printing debug material *)


val dprintf : flag -> ('a, Format.formatter, unit) format -> 'a
(** Print only if the flag is set *)

val stack_trace : flag
(** stack_trace flag *)

(** Command line arguments *)
module Opt : sig
  type spec = (Arg.key * Arg.spec * Arg.doc)

  val desc_debug_list : spec
  (** Option for printing the list of debug flags *)

  val option_list : unit -> bool
  (** Print the list of debug flag if requested (in this case return [true]).
      You should run this function after the plugins have been loaded. *)

  val desc_debug_all : spec
  (** Option for setting all the debug flags except the stopping one *)

  val desc_debug : spec
  (** Option for specifying a debug flag to set *)

  val desc_shortcut : string -> Arg.key -> Arg.doc -> spec
  (** Option for setting a specific flag *)

  val set_flags_selected : unit -> unit
  (** Set the flags selected by debug_all, debug or a shortcut.
      You should run this function after the plugins have been started.
  *)

end
