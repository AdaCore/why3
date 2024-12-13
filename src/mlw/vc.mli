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

(** {1 WhyML VC generators} *)

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

val warn_missing_diverges : Loc.warning_id

val vc : Env.env -> known_map -> Theory.theory_uc -> pdecl -> pdecl list

(**/**)

val expl_pre : Ident.attribute
val expl_post : Ident.attribute
val expl_xpost : Ident.attribute
val expl_assume : Ident.attribute
val expl_assert : Ident.attribute
val expl_check : Ident.attribute
val expl_lemma : Ident.attribute
val expl_absurd : Ident.attribute
val expl_for_bound : Ident.attribute
val expl_off_bound : Ident.attribute
val expl_loop_init : Ident.attribute
val expl_loop_keep : Ident.attribute
val expl_loop_vari : Ident.attribute
val expl_variant : Ident.attribute
val expl_type_inv : Ident.attribute
val expl_divergent : Ident.attribute

val print_expl : Ident.attribute Pp.pp
