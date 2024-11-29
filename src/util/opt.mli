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

(** {1 Combinators on [option] type} *)

val get_exn : exn -> 'a option -> 'a

val fold : ('b -> 'a -> 'b) -> 'b -> 'a option -> 'b
(** [fold f d o] returns [d] if [o] is [None], and
    [f d x] if [o] is [Some x] *)

val map_fold : ('a -> 'b -> 'a * 'b) -> 'a -> 'b option -> 'a * 'b option
