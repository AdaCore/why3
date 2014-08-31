(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Explanations *)

val goal_expl_task:
  root:bool -> Task.task -> Ident.ident * string option * Task.task

(** Shapes *)

val reset_dict : unit -> unit

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
val t_shape_task: ?version:int -> Task.task -> shape
  (** returns the shape of a given task *)

(** Checksums *)

type checksum
val print_checksum: Format.formatter -> checksum -> unit
val string_of_checksum: checksum -> string
val checksum_of_string: string -> checksum
val equal_checksum: checksum -> checksum -> bool
val dumb_checksum: checksum

val task_checksum : ?version:int -> Task.task -> checksum

val theory_checksum : ?version:int -> Theory.theory -> checksum

(** Pairing algorithm *)

module type S = sig
  type t
  val checksum : t -> checksum option
  val shape    : t -> shape
  val name     : t -> Ident.ident
end

module Pairing(Old: S)(New: S) : sig
  val associate: theory_was_fully_up_to_date:bool -> use_shapes:bool ->
    Old.t list -> New.t list -> (New.t * (Old.t * bool) option) list
    (** Associate new goals to (possibly) old goals
        Each new goal is mapped either to
        - [None]: no old goal associated
        - [Some (h, false)]: the matching is exact (same checksums)
        - [Some (h, true)]: inexact matching (thus proofs for the new goal 
          must be assumed obsolete)

        if [use_shapes] is set, the clever algorithm matching shapes is used,
        otherwise a simple association in the given order of goals is done.

        if [theory_was_fully_up_to_date] is set, then all resulting
        goals are marked as non-obsolete, whatever their checksums are.

        Note: in the output, goals appear in the same order as in [newgoals] *)

end
