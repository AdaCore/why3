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

(* Priority queue *)

module Make(X: Set.OrderedType) : sig

  type t

  type elt = X.t

  val create: dummy:elt -> t
    (** [dummy] will never be returned *)

  val is_empty: t -> bool

  val add: t -> elt -> unit
    (* inserts a new element *)

  exception Empty

  val get_min: t -> elt
    (* returns the minimal element (does not remove it)
       raises [Empty] if the queue is empty *)

  val remove_min: t -> unit
    (* removes the minimal element
       raises [Empty] if the queue is empty *)

  val extract_min: t -> elt
    (* removes and returns the minimal element
       raises [Empty] if the queue is empty *)

end
