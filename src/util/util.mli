(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Useful functions *)

val const : 'a -> 'b -> 'a

val const2 : 'a -> 'b -> 'c -> 'a

val const3 : 'a -> 'b -> 'c -> 'd -> 'a

val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c

val foldi : ('a -> int -> 'a) -> 'a -> int -> int -> 'a

val mapi : (int -> 'a) -> int -> int -> 'a list

val iterf : (float -> unit) -> float -> float -> float -> unit
(** [iterf f min max step] *)

(** Convert fold-like functions into [for_all] and [exists] functions.
    Predicates passed to [all], [all2], and [alld] may raise FoldSkip to
    signalize [false]. Predicates passed to [any], [any2], and [anyd] may
    raise FoldSkip to signalize [true]. *)

exception FoldSkip

val all_fn : ('a -> bool) -> 'z -> 'a -> bool
(** [all_fn pr z a] return true if [pr a] is true,
    otherwise raise FoldSkip *)

val any_fn : ('a -> bool) -> 'z -> 'a -> bool
(** [any_fn pr z a] return false if [pr a] is false,
    otherwise raise FoldSkip *)

val all2_fn : ('a -> 'b -> bool) -> 'z -> 'a -> 'b -> bool
(** [all2_fn pr z a b] return true if [pr a b] is true,
    otherwise raise FoldSkip *)

val any2_fn : ('a -> 'b -> bool) -> 'z -> 'a -> 'b -> bool
(** [any2_fn pr z a b] return false if [pr a b] is false,
    otherwise raise FoldSkip *)

type ('z,'a,'c) fold = ('z -> 'a -> 'z) -> 'z -> 'c -> 'z

val all : (bool,'a,'c) fold -> ('a -> bool) -> 'c -> bool
val any : (bool,'a,'c) fold -> ('a -> bool) -> 'c -> bool

type ('z,'a,'b,'c,'d) fold2 = ('z -> 'a -> 'b -> 'z) -> 'z -> 'c -> 'd -> 'z

val all2 : (bool,'a,'b,'c,'d) fold2 -> ('a -> 'b -> bool) -> 'c -> 'd -> bool
val any2 : (bool,'a,'b,'c,'d) fold2 -> ('a -> 'b -> bool) -> 'c -> 'd -> bool

type ('z,'a,'b,'c) foldd =
  ('z -> 'a -> 'z) -> ('z -> 'b -> 'z) -> 'z -> 'c -> 'z

val alld : (bool,'a,'b,'c) foldd -> ('a -> bool) -> ('b -> bool) -> 'c -> bool
val anyd : (bool,'a,'b,'c) foldd -> ('a -> bool) -> ('b -> bool) -> 'c -> bool

val ffalse : 'a -> bool
(** [ffalse] constant function [false] *)

val ttrue : 'a -> bool
(** [ttrue] constant function [true] *)


(* timing functions allow to measure CPU time consumption of parts of Why3 *)

val init_timing : unit -> unit
(* call this function to start measurements *)

val timing_step_completed : string -> unit
(* call this function to signal the completion of a processing step identified
   by a string. The consumed CPU time since the last call of init_timing or
   timing_step_completed will be considered as the time consumed by that
   processing step. If the function is called more than once with the same
   string argument, processing times will accumulate. *)

val get_timings : unit -> (string, float) Hashtbl.t
(* return the current timings obtained by calls to init_timing and
 * timing_step_completed *)
