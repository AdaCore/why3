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

(** Explanations *)

val arg_extra_expl_prefix : string * Arg.spec * string

val goal_expl_task:
  root:bool -> Task.task -> Ident.ident * string * Task.task

val search_attrs :
  (Ident.Sattr.t -> 'a list) -> Term.term -> 'a list
  (* [search_attrs callback f] traverses [f] in a top-down manner and calls the
     [callback] on the attribute set of all encountered nodes. As soon as the
     callback returns a non-empty list, the traversal is stopped and that list
     is returned. Raises exception Exit if the entire term has been traversed.
   *)

(** Shapes *)

(*
val reset_dict : unit -> unit
 *)

val current_shape_version : int

type shape
val string_of_shape: shape -> string
val shape_of_string: string -> shape
val equal_shape: shape -> shape -> bool
(* unused
val print_shape: Format.formatter -> shape -> unit
*)

(* val t_shape_buf : ?version:int -> Term.term -> shape *)
  (** returns the shape of a given term *)
val t_shape_task: ?version:int -> expl:string -> Task.task -> shape
  (** returns the shape of a given task *)

(** Checksums *)

type checksum
val print_checksum: Format.formatter -> checksum -> unit
val string_of_checksum: checksum -> string
val checksum_of_string: string -> checksum
val equal_checksum: checksum -> checksum -> bool
val dumb_checksum: checksum

val buffer_checksum : Buffer.t -> checksum

val task_checksum : ?version:int -> Task.task -> checksum

(** Pairing algorithm *)

module type S = sig
  type 'a t
  val checksum : 'a t -> checksum option
  val shape    : 'a t -> shape
  val name     : 'a t -> Ident.ident
end

module Pairing(Old: S)(New: S) : sig
  val associate:
    use_shapes:bool -> 'a Old.t list -> 'b New.t list ->
    ('b New.t * ('a Old.t * bool) option) list * 'a Old.t list
    (** Associate new goals to (possibly) old goals
        Each new goal is mapped either to
        - [None]: no old goal associated
        - [Some (h, false)]: the matching is exact (same checksums)
        - [Some (h, true)]: inexact matching (thus proofs for the new goal
          must be assumed obsolete)

        if [use_shapes] is set, the clever algorithm matching shapes is used,
        otherwise a simple association in the given order of goals is done.

        Note: in the output, goals appear in the same order as in [newgoals]

        the second list returned is the list of non-associated old goals.

     *)

end
