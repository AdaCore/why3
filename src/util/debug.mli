(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Debug flag handling} *)

type flag

val register_flag : desc:Pp.formatted -> string -> flag
(** Return the corresponding flag, after registering it if needed. *)

val register_info_flag : desc:Pp.formatted -> string -> flag
(** Return the corresponding flag, after registering it if needed.
    Info flags are set by [--debug-all] and must not change the behavior. *)

val list_flags : unit -> (string * flag * bool * Pp.formatted) list
(** List the known flags. The boolean component indicates an info flag. *)

val lookup_flag : string -> flag
(** Return the corresponding flag.
    @raise UnknownFlag if unknown. *)

(** Modify the state of a flag. *)

val set_flag : flag -> unit
val unset_flag : flag -> unit
val toggle_flag : flag -> unit

(** Return the state of a flag. *)

val test_flag : flag -> bool
val test_noflag : flag -> bool

val set_debug_formatter : Format.formatter -> unit
(** Set the formatter used when printing debug material. *)

val get_debug_formatter : unit -> Format.formatter
(** Get the formatter used when printing debug material. *)

val dprintf : flag -> ('a, Format.formatter, unit) format -> 'a
(** Print only if the flag is set. *)

val stack_trace : flag
(** "stack_trace" flag. *)



(** Command line arguments *)
module Args : sig
  type spec = Getopt.opt

  val desc_debug_list : spec
  (** Option for printing the list of debug flags. *)

  val option_list : unit -> bool
  (** Print the list of flags if requested (in this case return [true]).
      You should run this function after the plugins have been loaded. *)

  val desc_debug_all : spec
  (** Option for setting all info flags. *)

  val desc_debug : spec
  (** Option for specifying a debug flag to set. *)

  val desc_shortcut : string -> Getopt.key -> Getopt.doc -> spec
  (** Option for setting a specific flag. *)

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

  val record_timing : string -> (unit -> 'a) -> 'a
  (** Wrap a function call with this function in order to record its execution
    time in a global table. The cumulative timing and number of recordings for
    each name is stored. *)

  val add_timing : string -> float -> unit
  (** Record a raw timing obtained externally, e.g., from prover execution. *)

  val get_timings : unit -> (string, (float * int)) Hashtbl.t

end
