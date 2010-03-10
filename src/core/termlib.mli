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

open Ident
open Ty
open Term

(* generic term/fmla traversal *)

val t_map : (term -> term) -> (fmla -> fmla) -> term -> term
val f_map : (term -> term) -> (fmla -> fmla) -> fmla -> fmla

val t_fold : ('a -> term -> 'a) -> ('a -> fmla -> 'a) -> 'a -> term -> 'a
val f_fold : ('a -> term -> 'a) -> ('a -> fmla -> 'a) -> 'a -> fmla -> 'a

val t_all : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_all : (term -> bool) -> (fmla -> bool) -> fmla -> bool
val t_any : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_any : (term -> bool) -> (fmla -> bool) -> fmla -> bool

(* map/fold over free variables *)

val t_v_map : (vsymbol -> term) -> term -> term
val f_v_map : (vsymbol -> term) -> fmla -> fmla

val t_v_fold : ('a -> vsymbol -> 'a) -> 'a -> term -> 'a
val f_v_fold : ('a -> vsymbol -> 'a) -> 'a -> fmla -> 'a

val t_v_all : (vsymbol -> bool) -> term -> bool
val f_v_all : (vsymbol -> bool) -> fmla -> bool
val t_v_any : (vsymbol -> bool) -> term -> bool
val f_v_any : (vsymbol -> bool) -> fmla -> bool

(* variable occurrence check *)

val t_occurs : Svs.t -> term -> bool
val f_occurs : Svs.t -> fmla -> bool

val t_occurs_single : vsymbol -> term -> bool
val f_occurs_single : vsymbol -> fmla -> bool

(* substitution for variables *)

val t_subst : term Mvs.t -> term -> term
val f_subst : term Mvs.t -> fmla -> fmla

val t_subst_single : vsymbol -> term -> term -> term
val f_subst_single : vsymbol -> term -> fmla -> fmla

(* set of free variables *)

val t_freevars : Svs.t -> term -> Svs.t
val f_freevars : Svs.t -> fmla -> Svs.t

(* equality modulo alpha *)

val t_equal_alpha : term -> term -> bool
val f_equal_alpha : fmla -> fmla -> bool

(* occurrence check *)

val t_occurs_term : term -> term -> bool
val f_occurs_term : term -> fmla -> bool
val t_occurs_fmla : fmla -> term -> bool
val f_occurs_fmla : fmla -> fmla -> bool

val t_occurs_term_alpha : term -> term -> bool
val f_occurs_term_alpha : term -> fmla -> bool
val t_occurs_fmla_alpha : fmla -> term -> bool
val f_occurs_fmla_alpha : fmla -> fmla -> bool

(* term/fmla replacement *)

val t_subst_term : term -> term -> term -> term
val f_subst_term : term -> term -> fmla -> fmla
val t_subst_fmla : fmla -> fmla -> term -> term
val f_subst_fmla : fmla -> fmla -> fmla -> fmla

val t_subst_term_alpha : term -> term -> term -> term
val f_subst_term_alpha : term -> term -> fmla -> fmla
val t_subst_fmla_alpha : fmla -> fmla -> term -> term
val f_subst_fmla_alpha : fmla -> fmla -> fmla -> fmla

(* term/fmla matching modulo alpha in the pattern *)

val t_match : term -> term -> term Mvs.t -> term Mvs.t option
val f_match : fmla -> fmla -> term Mvs.t -> term Mvs.t option

