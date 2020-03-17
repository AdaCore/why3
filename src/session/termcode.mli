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

(* Backward compatible but not used in recent shape version *)
type shape

(* This shape representation is not just a classic "summary" of a task as
   [shape]. Each declaration shape of the whole session is recorded in the
   session (see Gshape.gshape for these global field) and associated to a
   unique index. The [bound_shape] is just the list of integers corresponding to
   the shapes of declarations.
   These shape are used from recent shape version *)
type bound_shape

val empty_bound_shape: bound_shape
val empty_shape: shape

type shape_v =
  | Old_shape of shape
  | Bound_shape of bound_shape

type sum_shape_version

val string_to_sum_shape_version : string -> sum_shape_version

val pp_sum_shape_version : Format.formatter -> sum_shape_version -> unit

(* True if a shape version represented as bound_shape false if it is shape *)
val is_bound_sum_shape_version: sum_shape_version -> bool

val current_sum_shape_version : sum_shape_version

val shape_of_string: version:sum_shape_version -> string -> shape_v
val string_of_shape: shape_v -> string

val t_shape_task: version:sum_shape_version -> expl:string -> Task.task -> shape
(** returns the shape of a given task. returns [empty_shape] for unrecognized versions *)

(* This modules handles the session part of the new [bound_shape]. A [gshape]
   is now included in the session *)
module Gshape : sig

  (* This type records the mapping between integers and shapes' declaration *)
  type gshape

  val create              : unit   -> gshape
  val copy                : gshape -> gshape -> unit
  val clear_gs            : gshape -> unit

  (* Add the following string shape to the gshape *)
  val add_shape_g         : gshape -> string -> unit
  (* Write all added shape (in the order they were saved) on given channel *)
  val write_shape_to_file : gshape -> Compress.Compress_z.out_channel -> unit
  (* Convert a bound_shape back into a shape. This uses the added shape and
     replace first two integers (expl and goal) with their shape *)
  val goal_and_expl_shapes  : gshape -> bound_shape -> shape

  val t_bound_shape_task:
    gshape -> version:sum_shape_version -> expl:string -> Task.task -> bound_shape

  val empty_bshape: bound_shape
end

(** Checksums *)

type checksum
val print_checksum: Format.formatter -> checksum -> unit
val string_of_checksum: checksum -> string
val checksum_of_string: string -> checksum
val equal_checksum: checksum -> checksum -> bool
val dumb_checksum: checksum

val buffer_checksum : Buffer.t -> checksum

val task_checksum : ?version:sum_shape_version -> Task.task -> checksum

(** Pairing algorithm *)

module type S = sig
  type 'a t
  val checksum : 'a t -> checksum option
  val shape    : 'a t -> shape * bound_shape
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
