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

open Pdecl

val sp_attr : Ident.attribute (* switch to fast WP *)
val wp_attr : Ident.attribute (* switch to classical WP (Cfun only) *)
val kp_attr : Ident.attribute (* preserve preconditions after the call *)
val wb_attr : Ident.attribute (* treat an abstract block as a whitebox *)
val nt_attr : Ident.attribute (* allow non-terminating calls and loops *)

val set_infer_invs :
  (Ident.Sattr.t -> Env.env -> Decl.known_map -> known_map -> Expr.expr ->
   Ity.cty -> (Expr.expr * Term.term) list) -> unit
(* adds a function to infer invariants during the VC generation *)

val vc : Env.env -> known_map -> Theory.theory_uc -> pdecl -> pdecl list
