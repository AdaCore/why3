(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

(** eliminate let *)
val remove_let_t : Term.term -> Term.term
val remove_let_f : Term.fmla -> Term.fmla

val eliminate_let : Task.task Register.trans_reg


(** eliminate ite, ie if then else in term *)
val remove_ite_t : Term.term -> (Term.fmla * Term.term) list
val remove_ite_f : Term.fmla -> Term.fmla
val remove_ite_decl : Decl.decl -> Decl.decl list

val eliminate_ite : Task.task Register.trans_reg

(** eliminate ite, ie if then else in term *)
val remove_if_then_else_t : Term.term -> Term.term
val remove_if_then_else_f : Term.fmla -> Term.fmla

val eliminate_if_then_else : Task.task Register.trans_reg

