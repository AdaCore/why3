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

open Ty

type label

(** Variable symbols *)

type vsymbol = private {
  vs_name : Name.t;
  vs_ty : ty;
  vs_tag : int;
}

module Svs : Set.S with type elt = vsymbol
module Mvs : Map.S with type key = vsymbol

val create_vsymbol : Name.t -> ty -> vsymbol

(** Function symbols *)

type fsymbol = private {
  fs_name   : Name.t;
  fs_scheme : ty list * ty;
  fs_constr : bool;
  fs_tag    : int;
}

val create_fsymbol : Name.t -> ty list * ty -> bool -> fsymbol

module Sfs : Set.S with type elt = fsymbol
module Mfs : Map.S with type key = fsymbol

(** Predicate symbols *)

type psymbol = private {
  ps_name   : Name.t;
  ps_scheme : ty list;
  ps_tag    : int;
}

val create_psymbol : Name.t -> ty list -> psymbol

module Sps : Set.S with type elt = psymbol
module Mps : Map.S with type key = psymbol

(** Patterns *)

type pattern = private {
  pat_node : pattern_node;
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node = private
  | Pwild
  | Pvar of vsymbol
  | Papp of fsymbol * pattern list
  | Pas  of pattern * vsymbol

(* smart constructors for patterns *)

val pat_wild : ty -> pattern
val pat_var : vsymbol -> pattern
val pat_app : fsymbol -> pattern list -> ty -> pattern
val pat_as  : pattern -> vsymbol -> pattern

val pat_map : (pattern -> pattern) -> pattern -> pattern
val pat_fold : ('a -> pattern -> 'a) -> 'a -> pattern -> 'a
val pat_forall : (pattern -> bool) -> pattern -> bool
val pat_exists : (pattern -> bool) -> pattern -> bool

val pat_equal_alpha : pattern -> pattern -> bool

(** Terms and formulas *)

type quant =
  | Fforall
  | Fexists

type binop =
  | Fand
  | For
  | Fimplies
  | Fiff

type term = private {
  t_node : term_node;
  t_label : label list;
  t_ty : ty;
  t_tag : int;
}

and fmla = private {
  f_node : fmla_node;
  f_label : label list;
  f_tag : int;
}

and term_node = private
  | Tbvar of int
  | Tvar of vsymbol
  | Tapp of fsymbol * term list
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of fmla_bound

and fmla_node = private
  | Fapp of psymbol * term list
  | Fquant of quant * fmla_bound
  | Fbinop of binop * fmla * fmla
  | Fnot of fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * fmla_bound
  | Fcase of term * fmla_branch list

and term_bound

and fmla_bound

and term_branch

and fmla_branch

module Mterm : Map.S with type key = term
module Sterm : Set.S with type elt = term
module Mfmla : Map.S with type key = fmla
module Sfmla : Set.S with type elt = fmla

(* smart constructors for term *)

val t_var : vsymbol -> term
val t_app : fsymbol -> term list -> ty -> term
val t_let : vsymbol -> term -> term -> term
val t_case : term -> (pattern * term) list -> ty -> term
val t_eps : vsymbol -> fmla -> term

val t_label : label list -> term -> term
val t_label_add : label -> term -> term

(* smart constructors for fmla *)

val f_app : psymbol -> term list -> fmla
val f_forall : vsymbol -> fmla -> fmla
val f_exists : vsymbol -> fmla -> fmla
val f_quant : quant -> vsymbol -> fmla -> fmla
val f_and : fmla -> fmla -> fmla
val f_or : fmla -> fmla -> fmla
val f_implies : fmla -> fmla -> fmla
val f_iff : fmla -> fmla -> fmla
val f_binary : binop -> fmla -> fmla -> fmla
val f_not : fmla -> fmla
val f_true : fmla
val f_false : fmla
val f_if : fmla -> fmla -> fmla -> fmla
val f_let : vsymbol -> term -> fmla -> fmla
val f_case :  term -> (pattern * fmla) list -> fmla

val f_label : label list -> fmla -> fmla
val f_label_add : label -> fmla -> fmla

(* bindings *)

val t_open_bound : term_bound -> vsymbol * term
val t_open_branch : term_branch -> pattern * Svs.t * term

val f_open_bound : fmla_bound -> vsymbol * fmla
val f_open_branch : fmla_branch -> pattern * Svs.t * fmla

(* safe opening map/fold *)

val t_map_open : (term -> term) -> (fmla -> fmla) -> term -> term
val f_map_open : (term -> term) -> (fmla -> fmla) -> fmla -> fmla

val t_fold_open : ('a -> term -> 'a) -> ('a -> fmla -> 'a)
                                         -> 'a -> term -> 'a

val f_fold_open : ('a -> term -> 'a) -> ('a -> fmla -> 'a)
                                         -> 'a -> fmla -> 'a

val t_forall_open : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_forall_open : (term -> bool) -> (fmla -> bool) -> fmla -> bool
val t_exists_open : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_exists_open : (term -> bool) -> (fmla -> bool) -> fmla -> bool

(* safe transparent map/fold *)

val t_map_trans : (term -> term) -> (fmla -> fmla) -> term -> term
val f_map_trans : (term -> term) -> (fmla -> fmla) -> fmla -> fmla

val t_fold_trans : ('a -> term -> 'a) -> ('a -> fmla -> 'a)
                                          -> 'a -> term -> 'a

val f_fold_trans : ('a -> term -> 'a) -> ('a -> fmla -> 'a)
                                          -> 'a -> fmla -> 'a

val t_forall_trans : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_forall_trans : (term -> bool) -> (fmla -> bool) -> fmla -> bool
val t_exists_trans : (term -> bool) -> (fmla -> bool) -> term -> bool
val f_exists_trans : (term -> bool) -> (fmla -> bool) -> fmla -> bool

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

(* USE PHYSICAL EQUALITY *)
(*
(* equality *)

val t_equal : term -> term -> bool
val f_equal : fmla -> fmla -> bool
*)

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

