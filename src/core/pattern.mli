(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Compilation of pattern-matching *)

open Ty
open Term

module type Action = sig
  type action
  type branch
  val mk_let : vsymbol -> term -> action -> action
  val mk_branch : pattern -> action -> branch
  val mk_case : term -> branch list -> action
end

exception ConstructorExpected of lsymbol * ty
exception NonExhaustive of pattern list

module Compile (X : Action) : sig
  val compile : (tysymbol -> lsymbol list) ->
    term list -> (pattern list * X.action) list -> X.action

  val compile_bare :
    term list -> (pattern list * X.action) list -> X.action
  (** [compile_bare] does not compute non-covered patterns *)
end

module CompileTerm : sig
  val compile : (tysymbol -> lsymbol list) ->
    term list -> (pattern list * term) list -> term

  val compile_bare :
    term list -> (pattern list * term) list -> term
end
