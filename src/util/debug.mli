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

(** Debug flag handling *)

type flag

val register_flag : desc:Pp.formatted -> string -> flag
(** register a new flag. It is allowed to register twice the same flag *)

val register_info_flag : desc:Pp.formatted -> string -> flag
(** register a new info flag. It is allowed to register twice the same flag.
    Info flags are set by --debug-all and must not change the behaviour. *)

val list_flags : unit -> (string * flag * bool * Pp.formatted) list
(** list the known flags *)

val lookup_flag : string -> flag
(** get the flag *)

val is_info_flag : string -> bool
(** test if the flag is an info flag *)

val flag_desc : string -> Pp.formatted
(** get the description of the flag *)

(** Modify the state of a flag *)
val set_flag : flag -> unit
val unset_flag : flag -> unit
val toggle_flag : flag -> unit

(** Return the state of the flag *)
val test_flag : flag -> bool
val test_noflag : flag -> bool

val set_debug_formatter : Format.formatter -> unit
(** Set the formatter used when printing debug material *)

val get_debug_formatter : unit -> Format.formatter
(** Get the formatter used when printing debug material *)

val dprintf : flag -> ('a, Format.formatter, unit) format -> 'a
(** Print only if the flag is set *)

val stack_trace : flag
(** stack_trace flag *)



(** Command line arguments *)
module Args : sig
  type spec = (Arg.key * Arg.spec * Arg.doc)

  val desc_debug_list : spec
  (** Option for printing the list of debug flags *)

  val option_list : unit -> bool
  (** Print the list of flags if requested (in this case return [true]).
      You should run this function after the plugins have been loaded. *)

  val desc_debug_all : spec
  (** Option for setting all info flags *)

  val desc_debug : spec
  (** Option for specifying a debug flag to set *)

  val desc_shortcut : string -> Arg.key -> Arg.doc -> spec
  (** Option for setting a specific flag *)

  val set_flags_selected : ?silent:bool -> unit -> unit
  (** Set the flags selected by debug_all, debug or a shortcut.
      When called before the plugins are loaded, pass [~silent:true] to
      prevent errors due to unknown plugin flags. *)
end

val stats: flag
type 'a stat

module Stats: sig
  (** Stats *)

  val register:
    print:(Format.formatter -> 'a -> unit) ->
    name:string ->
    init:'a -> 'a stat

  val mod0: 'a stat -> ('a -> 'a) -> unit
  val mod1: 'a stat -> ('a -> 'b -> 'a) -> 'b -> unit
  val mod2: 'a stat -> ('a -> 'b -> 'c -> 'a) -> 'b -> 'c -> unit

  val register_int: name:string -> init:int -> int stat
  val incr: int stat -> unit
  val decr: int stat -> unit

  val print: unit -> unit
end
