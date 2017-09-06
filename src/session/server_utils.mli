(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


val get_session_dir : allow_mkdir:bool -> string Queue.t -> string
(** [get_session_dir q] analyses the queue of filenames [q] and
    returns the session directory from it.

    That directory is created if it does not exists and [allow_mkdir]
    is true.

    raises [Invalid_arg s] with some appropriate explnation [s] if no
    valid directory can be extracted.

    The first element of queue [q] is removed if it is not a file to
    load later in the session.

 *)

(** Simple queries *)

(* The id you are trying to use is undefined *)
exception Undefined_id of string
(* Bad number of arguments *)
exception Number_of_arguments

type query =
  | Qnotask of (Controller_itp.controller -> string list -> string)
  | Qtask of (Controller_itp.controller -> Trans.naming_table -> string list -> string)


val print_id: 'a -> Trans.naming_table -> string list -> string
val search_id: 'a -> Trans.naming_table -> string list -> string

val list_strategies : Controller_itp.controller -> (string * string) list
val list_provers: Controller_itp.controller -> _ -> string
val list_transforms: unit -> (string * Pp.formatted) list
val list_transforms_query: _ -> _ -> string
(* val help_on_queries: Format.formatter -> (string * string * 'a) list -> unit *)
val load_strategies: Controller_itp.controller -> unit


(** Command line parsing tools *)

val return_prover: string -> Whyconf.config -> Whyconf.config_prover option

type command =
  | Transform    of string * Trans.gentrans * string list
  | Prove        of Whyconf.config_prover * Call_provers.resource_limit
  | Strategies   of string
  | Edit         of Whyconf.config_prover
  | Help_message of string
  | Query        of string
  | QError       of string
  | Other        of string * string list

val interp:
  (string * query) Stdlib.Hstr.t ->
  Controller_itp.controller ->
  Session_itp.proofNodeID option -> string -> command


val get_first_unproven_goal_around:
    proved:('a -> bool) ->
      children:('a -> 'a list) ->
        get_parent:('a -> 'a option) ->
          is_goal:('a -> bool) ->
            is_pa:('a -> bool) -> 'a -> 'a option
