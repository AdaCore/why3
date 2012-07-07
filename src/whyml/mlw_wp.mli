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

open Why3
open Theory
open Mlw_ty
open Mlw_ty.T
open Mlw_decl
open Mlw_expr

(** WP-only builtins *)

val ts_mark : Ty.tysymbol
val ty_mark : Ty.ty

val fs_old : Term.lsymbol
val fs_at  : Term.lsymbol

val th_mark : Theory.theory

val fs_setmark : Term.lsymbol
val e_setmark  : expr

(** Weakest preconditions *)

val wp_val: Env.env -> known_map -> theory_uc -> val_decl -> theory_uc
val wp_let: Env.env -> known_map -> theory_uc -> let_defn -> theory_uc
val wp_rec: Env.env -> known_map -> theory_uc -> rec_defn list -> theory_uc
