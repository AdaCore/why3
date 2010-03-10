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

(** Variable symbols *)

type vsymbol = private {
  vs_name : ident;
  vs_ty : ty;
}

module Svs : Set.S with type elt = vsymbol
module Mvs : Map.S with type key = vsymbol
module Hvs : Hashtbl.S with type key = vsymbol

val create_vsymbol : preid -> ty -> vsymbol

(** Function and predicate symbols *)

type lsymbol = private {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
  ls_constr : bool;
}

val create_lsymbol : preid -> ty list -> ty option -> bool -> lsymbol
val create_fsymbol : preid -> ty list -> ty -> lsymbol
val create_fconstr : preid -> ty list -> ty -> lsymbol
val create_psymbol : preid -> ty list -> lsymbol

module Sls : Set.S with type elt = lsymbol
module Mls : Map.S with type key = lsymbol
module Hls : Hashtbl.S with type key = lsymbol

(** Exceptions *)

exception BadArity
exception NonLinear of vsymbol
exception ConstructorExpected of lsymbol
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol

(** Patterns *)

type pattern = private {
  pat_node : pattern_node;
  pat_ty : ty;
  pat_tag : int;
}

and pattern_node = private
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Pas  of pattern * vsymbol

(* smart constructors for patterns *)

val pat_wild : ty -> pattern
val pat_var : vsymbol -> pattern
val pat_app : lsymbol -> pattern list -> ty -> pattern
val pat_as  : pattern -> vsymbol -> pattern

(* generic traversal functions *)

val pat_map : (pattern -> pattern) -> pattern -> pattern
val pat_fold : ('a -> pattern -> 'a) -> 'a -> pattern -> 'a
val pat_all : (pattern -> bool) -> pattern -> bool
val pat_any : (pattern -> bool) -> pattern -> bool

(** Terms and formulas *)

type label = string

type quant =
  | Fforall
  | Fexists

type binop =
  | Fand
  | For
  | Fimplies
  | Fiff

type real_constant =
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of string
  | ConstReal of real_constant

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
  | Tconst of constant
  | Tapp of lsymbol * term list
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of fmla_bound

and fmla_node = private
  | Fapp of lsymbol * term list
  | Fquant of quant * fmla_quant
  | Fbinop of binop * fmla * fmla
  | Fnot of fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * fmla_bound
  | Fcase of term * fmla_branch list

and term_bound

and fmla_bound

and fmla_quant

and term_branch

and fmla_branch

and trigger_elt =
  | TrTerm of term
  | TrFmla of fmla

and trigger = trigger_elt list

module Mterm : Map.S with type key = term
module Sterm : Set.S with type elt = term
module Mfmla : Map.S with type key = fmla
module Sfmla : Set.S with type elt = fmla

(* smart constructors for term *)

val t_var : vsymbol -> term
val t_const : constant -> ty -> term
val t_app : lsymbol -> term list -> ty -> term
val t_let : vsymbol -> term -> term -> term
val t_case : term -> (pattern * term) list -> ty -> term
val t_eps : vsymbol -> fmla -> term

val t_label : label list -> term -> term
val t_label_add : label -> term -> term
val t_label_copy : term -> term -> term

(* smart constructors for fmla *)

val f_app : lsymbol -> term list -> fmla
val f_forall : vsymbol list -> trigger list -> fmla -> fmla
val f_exists : vsymbol list -> trigger list -> fmla -> fmla
val f_quant : quant -> vsymbol list -> trigger list -> fmla -> fmla
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
val f_label_copy : fmla -> fmla -> fmla

(* open bindings *)

val t_open_bound : term_bound -> vsymbol * term
val f_open_bound : fmla_bound -> vsymbol * fmla

val t_open_branch : term_branch -> pattern * Svs.t * term
val f_open_branch : fmla_branch -> pattern * Svs.t * fmla

val f_open_quant : fmla_quant -> vsymbol list * trigger list * fmla

val f_open_forall : fmla -> vsymbol list * fmla
val f_open_exists : fmla -> vsymbol list * fmla

(* unsafe open with unprotected de Bruijn indices *)

val t_open_bound_unsafe : term_bound -> vsymbol * term
val f_open_bound_unsafe : fmla_bound -> vsymbol * fmla

val t_open_branch_unsafe : term_branch -> pattern * int * term
val f_open_branch_unsafe : fmla_branch -> pattern * int * fmla

val f_open_quant_unsafe :
  fmla_quant -> vsymbol list * int * trigger list * fmla

val f_open_forall_unsafe : fmla -> vsymbol list * int * fmla
val f_open_exists_unsafe : fmla -> vsymbol list * int * fmla

(* unsafe traversal with unprotected de Bruijn indices *)

val t_map_unsafe : (int -> term -> term) ->
                   (int -> fmla -> fmla) -> int -> term -> term

val f_map_unsafe : (int -> term -> term) ->
                   (int -> fmla -> fmla) -> int -> fmla -> fmla

val t_fold_unsafe : (int -> 'a -> term -> 'a) ->
                    (int -> 'a -> fmla -> 'a) -> int -> 'a -> term -> 'a

val f_fold_unsafe : (int -> 'a -> term -> 'a) ->
                    (int -> 'a -> fmla -> 'a) -> int -> 'a -> fmla -> 'a

val t_all_unsafe : (int -> term -> bool) ->
                   (int -> fmla -> bool) -> int -> term -> bool

val f_all_unsafe : (int -> term -> bool) ->
                   (int -> fmla -> bool) -> int -> fmla -> bool

val t_any_unsafe : (int -> term -> bool) ->
                   (int -> fmla -> bool) -> int -> term -> bool

val f_any_unsafe : (int -> term -> bool) ->
                   (int -> fmla -> bool) -> int -> fmla -> bool

(* trigger traversal *)

val tr_map : (term -> term) ->
             (fmla -> fmla) -> trigger list -> trigger list

val tr_fold : ('a -> term -> 'a) ->
              ('a -> fmla -> 'a) -> 'a -> trigger list -> 'a

(* map/fold over symbols *)

val t_s_map : (tysymbol -> tysymbol) -> (lsymbol -> lsymbol) -> term -> term
val f_s_map : (tysymbol -> tysymbol) -> (lsymbol -> lsymbol) -> fmla -> fmla

val t_s_fold :
  ('a -> tysymbol -> 'a) -> ('a -> lsymbol -> 'a) -> 'a -> term -> 'a

val f_s_fold :
  ('a -> tysymbol -> 'a) -> ('a -> lsymbol -> 'a) -> 'a -> fmla -> 'a

val t_s_all : (tysymbol -> bool) -> (lsymbol -> bool) -> term -> bool
val f_s_all : (tysymbol -> bool) -> (lsymbol -> bool) -> fmla -> bool
val t_s_any : (tysymbol -> bool) -> (lsymbol -> bool) -> term -> bool
val f_s_any : (tysymbol -> bool) -> (lsymbol -> bool) -> fmla -> bool

(* built-in symbols *)

val ps_equ : lsymbol
val ps_neq : lsymbol

val f_equ : term -> term -> fmla
val f_neq : term -> term -> fmla

