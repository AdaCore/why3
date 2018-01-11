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

(** {1 Weakest preconditions} *)

open Theory
open Mlw_ty.T
open Mlw_decl
open Mlw_expr

(** {2 WP-only builtins} *)

val lemma_label : Ident.label

val fs_at  : Term.lsymbol
val fs_old : Term.lsymbol

val t_at_old : Term.term -> Term.term

val mark_theory : Theory.theory
val th_mark_at  : Theory.theory
val th_mark_old : Theory.theory

val fs_now : Term.lsymbol
val e_now : expr

val remove_old : Term.term -> Term.term

val full_invariant :
  Decl.known_map -> Mlw_decl.known_map -> Term.vsymbol -> ity -> Term.term

(** {2 Weakest precondition computations} *)

val wp_val:
  wp:bool -> Env.env -> known_map -> theory_uc -> let_sym  -> theory_uc
val wp_let:
  wp:bool -> Env.env -> known_map -> theory_uc -> let_defn -> theory_uc
val wp_rec:
  wp:bool -> Env.env -> known_map -> theory_uc -> fun_defn list -> theory_uc
