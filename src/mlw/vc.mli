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

open Pdecl

val sp_label : Ident.label (* switch to fast WP *)
val wp_label : Ident.label (* switch to classical WP (Cfun only) *)
val kp_label : Ident.label (* preserve preconditions after the call *)
val wb_label : Ident.label (* treat an abstract block as a whitebox *)

val vc : Env.env -> known_map -> Theory.theory_uc -> pdecl -> pdecl list
