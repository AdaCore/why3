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

(** Hashtables with weak key used for memoization *)

type tag

val dummy_tag : tag

val create_tag : int -> tag

val tag_equal : tag -> tag -> bool

val tag_hash : tag -> int

module type S = sig

  type key

  type 'a t

  val create : int -> 'a t
    (* create a hashtbl with weak keys *)

  val clear : 'a t -> unit

  val copy : 'a t -> 'a t

  val find : 'a t -> key -> 'a
    (* find the value bound to a key.
       Raises Not_found if there is no binding *)

  val mem : 'a t -> key -> bool
    (* test if a key is bound *)

  val set : 'a t -> key -> 'a -> unit
    (* bind the key _once_ with the given value *)

  val remove : 'a t -> key -> unit
    (* remove the value *)

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val iterk : (key -> unit) -> 'a t -> unit

  val foldk : (key -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val length : 'a t -> int

  val memoize : int -> (key -> 'a) -> (key -> 'a)
    (* create a memoizing function *)

  val memoize_rec : int -> ((key -> 'a) -> (key -> 'a)) -> (key -> 'a)
    (* create a memoizing recursive function *)

  val memoize_option : int -> (key option -> 'a) -> (key option -> 'a)
    (* memoizing functions on option types *)

end

module type Weakey =
sig
  type t
  val tag : t -> tag
end

module Make (S : Weakey) : S with type key = S.t

