(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

type label

(** Types *)

module Ty : sig

  type tvsymbol = Name.t

  (* type symbols and types *)

  type tysymbol = private {
    ts_name : Name.t;
    ts_args : tvsymbol list;
    ts_def  : ty option;
    ts_alg  : bool;
    ts_tag  : int;
  }

  and ty = private {
    ty_node : ty_node;
    ty_tag  : int;
  }

  and ty_node = private
    | Tyvar of tvsymbol
    | Tyapp of tysymbol * ty list

  val create_tysymbol : Name.t -> tvsymbol list -> ty option
                                                -> bool -> tysymbol

  val ty_var : tvsymbol -> ty
  val ty_app : tysymbol -> ty list -> ty

end

type tvsymbol = Ty.tvsymbol
type tysymbol = Ty.tysymbol
type ty = Ty.ty

(** Variable symbols *)

type vsymbol = private {
  vs_name : Name.t;
  vs_ty : ty;
  vs_tag : int;
}

module Mvs : Map.S with type key = vsymbol
module Svs : Set.S with type elt = vsymbol

type vsymbol_set = Svs.t

val create_vsymbol : Name.t -> ty -> vsymbol

(** Function symbols *)

type fsymbol = private {
  fs_name   : Name.t;
  fs_scheme : ty list * ty;
  fs_constr : bool;
  fs_tag    : int;
}

val create_fsymbol : Name.t -> ty list * ty -> bool -> fsymbol

(** Predicate symbols *)

type psymbol = private {
  ps_name   : Name.t;
  ps_scheme : ty list;
  ps_tag    : int;
}

val create_psymbol : Name.t -> ty list -> psymbol

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
  | Pas of pattern * vsymbol

(* smart constructors for patterns *)

val pat_wild : ty -> pattern
val pat_var : vsymbol -> pattern
val pat_app : fsymbol -> pattern list -> ty -> pattern
val pat_as : pattern -> vsymbol -> pattern

(** Terms and formulas *)

type quant =
  | Fforall
  | Fexists

type binop =
  | Fand
  | For
  | Fimplies
  | Fiff

type unop =
  | Fnot

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
  | Tcase of term * tbranch list
  | Tlet of term * bind_term
  | Teps of bind_fmla

and fmla_node = private
  | Fapp of psymbol * term list
  | Fquant of quant * bind_fmla
  | Fbinop of binop * fmla * fmla
  | Funop of unop * fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * bind_fmla
  | Fcase of term * fbranch list

and bind_term

and bind_fmla

and tbranch

and fbranch

(* smart constructors for term *)

val t_var : vsymbol -> term
val t_app : fsymbol -> term list -> ty -> term
val t_case : term -> (pattern * term) list -> ty -> term
val t_let : vsymbol -> term -> term -> term
val t_eps : vsymbol -> fmla -> term

val t_label : label list -> term -> term
val t_label_add : label -> term -> term

(* smart constructors for fmla *)

val f_app : psymbol -> term list -> fmla

val f_true : fmla
val f_false : fmla
val f_and : fmla -> fmla -> fmla
val f_or : fmla -> fmla -> fmla
val f_implies : fmla -> fmla -> fmla
val f_iff : fmla -> fmla -> fmla
val f_not : fmla -> fmla

val f_forall : vsymbol -> fmla -> fmla
val f_exists : vsymbol -> fmla -> fmla

val f_if : fmla -> fmla -> fmla -> fmla
val f_let : vsymbol -> term -> fmla -> fmla
val f_case :  term -> (pattern * fmla) list -> fmla

val f_label : label list -> fmla -> fmla
val f_label_add : label -> fmla -> fmla

(* transformations ? *)

(* val map : (term -> term) -> term -> term *)

(* bindings *)

val open_bind_term : bind_term -> vsymbol * term
val open_tbranch : tbranch -> pattern * vsymbol_set * term

val open_bind_fmla : bind_fmla -> vsymbol * fmla
val open_fbranch : fbranch -> pattern * vsymbol_set * fmla

(* equality *)

val t_equal : term -> term -> bool
val t_alpha_equal : term -> term -> bool

val f_equal : fmla -> fmla -> bool
val f_alpha_equal : fmla -> fmla -> bool
