(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ity
open Expr
open Term

val print_inferred_invs : Debug.flag

val infer_loops : Sattr.t -> Env.env -> Decl.known_map ->
                  Pdecl.known_map -> expr -> cty -> (expr * term) list

val register_hook : ((expr * term) list -> unit) -> unit
(** registers a function to be applied on the inferred invariants *)
