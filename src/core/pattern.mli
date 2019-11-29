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

(* Pattern compilation *)

open Ty
open Term

exception ConstructorExpected of lsymbol * ty
exception NonExhaustive of pattern list

val compile :
  get_constructors:(tysymbol -> lsymbol list) ->
  mk_case:(term -> (pattern * 'a) list -> 'a) ->
  mk_let:(vsymbol -> term -> 'a -> 'a) ->
  term list -> (pattern list * 'a) list -> 'a
  (** [compile get_constructors mk_case mk_let terms branches]
      returns a composition of match- and let-terms equivalent
      to [match terms with branches], where every pattern is
      either a constructor applied to a list of variables, or
      a wildcard pattern.

      Raises [NonExhaustive patterns] where [patterns] is the
      list of non-covered patterns. The check is permissive:
      [match Cons t tl with Cons x xl -> ...] is accepted and
      compiled into [match t, tl with x, xl -> ...]. *)

val compile_bare :
  mk_case:(term -> (pattern * 'a) list -> 'a) ->
  mk_let:(vsymbol -> term -> 'a -> 'a) ->
  term list -> (pattern list * 'a) list -> 'a
  (** [compile_bare] does not compute non-covered patterns *)

val check_compile :
  get_constructors:(tysymbol -> lsymbol list) ->
  term list -> pattern list list -> unit
  (** [check_compile] verfies that the pattern list is exhaustive
      and raises [NonExhaustive patterns] if it is not. If the term
      list argument is empty, it is treated as a list of variables
      of appropriate types. *)

val is_exhaustive : term list -> pattern list list -> bool
  (** [is_exhaustive] checks if the pattern list is exhaustive.
      If the term list argument is empty, it is treated as a list
      of variables of appropriate types. *)
