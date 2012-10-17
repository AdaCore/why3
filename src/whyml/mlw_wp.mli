(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_decl
open Mlw_expr

(** WP-only builtins *)

val ts_mark : Ty.tysymbol
val ty_mark : Ty.ty

val fs_at  : Term.lsymbol
val fs_old : Term.lsymbol

val th_mark_at  : Theory.theory
val th_mark_old : Theory.theory

val e_now : expr

val pv_old : pvsymbol
val remove_old : Term.term -> Term.term

val full_invariant :
  Decl.known_map -> Mlw_decl.known_map -> Term.vsymbol -> ity -> Term.term

(** Weakest preconditions *)

val wp_val: Env.env -> known_map -> theory_uc -> let_sym  -> theory_uc
val wp_let: Env.env -> known_map -> theory_uc -> let_defn -> theory_uc
val wp_rec: Env.env -> known_map -> theory_uc -> fun_defn list -> theory_uc


(** Efficient weakest preconditions *)

val fast_wp: Debug.flag

val fast_wp_val: Env.env -> known_map -> theory_uc -> let_sym  -> theory_uc
val fast_wp_let: Env.env -> known_map -> theory_uc -> let_defn -> theory_uc
val fast_wp_rec: Env.env -> known_map -> theory_uc -> fun_defn list -> theory_uc

