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

(** Association tables over hashable types *)

val hash : 'a -> int
  (** the same as Hashtbl.hash *)

module type S =
sig
  include Hashtbl.S

  val find_def : 'a t -> 'a -> key -> 'a
  (** return the first binding or the given value if none found *)

  val find_opt : 'a t -> key -> 'a option
  (** return the first binding or None if none found *)

  val find_exn : 'a t -> exn -> key -> 'a
  (** return the first binding or raise the given exception if none found *)

  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  (** a shortcut less efficient than possible *)

  val memo : int -> (key -> 'a) -> key -> 'a
  (** convenience function, memoize a function *)

  val is_empty : 'a t -> bool
  (** test if the hashtbl is empty *)
end

module type Private =
sig
  (** Private Hashtbl *)
  type 'a t
  type key

  val find : 'a t -> key -> 'a
  (** Same as {!Hashtbl.find} *)

  val find_def : 'a t -> 'a -> key -> 'a
  (** return the first binding or the given value if none found *)

  val find_opt : 'a t -> key -> 'a option
  (** return the first binding or None if none found *)

  val find_exn : 'a t -> exn -> key -> 'a
  (** return the first binding or raise the given exception if none found *)

  val map : (key -> 'a -> 'b) -> 'a t -> 'b t
  (** a shortcut less efficient than possible *)

  val iter : (key -> 'a -> unit) -> 'a t -> unit
  (** Same as {!Hashtbl.iter} *)

  val fold : (key -> 'a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc
  (** Same as {!Hashtbl.fold} *)

  val mem : 'a t -> key -> bool
  (** Same as {!Hashtbl.mem} *)

  val length : 'a t -> int
  (** Same as {!Hashtbl.length} *)

  val is_empty : 'a t -> bool
  (** test if the hashtbl is empty *)
end

module Make (X:Hashtbl.HashedType) : S with type key = X.t
