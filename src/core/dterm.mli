(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term

(** Types *)

type dty

val dty_fresh : unit -> dty

val dty_of_ty : ty -> dty

(** Patterns, terms, and formulas *)

type dpattern = private {
  dp_node : dpattern_node;
  dp_dty  : dty;
  dp_loc  : Loc.position option;
}

and dpattern_node =
  | DPwild
  | DPvar of preid
  | DPapp of lsymbol * dpattern list
  | DPor of dpattern * dpattern
  | DPas of dpattern * preid

type dterm = private {
  dt_node  : dterm_node;
  dt_dty   : dty option;
  dt_label : Slab.t;
  dt_loc   : Loc.position option;
  dt_uloc  : Loc.position option;
}

and dterm_node =
  | DTvar of string
  | DTconst of Number.constant
  | DTapp of lsymbol * dterm list
  | DTif of dterm * dterm * dterm
  | DTlet of dterm * preid * dterm
  | DTcase of dterm * (dpattern * dterm) list
  | DTeps of preid * dty * dterm
  | DTquant of quant * (preid * dty) list * dterm list list * dterm
  | DTbinop of binop * dterm * dterm
  | DTnot of dterm
  | DTtrue
  | DTfalse

(** Environment *)

exception TermExpected
exception FmlaExpected
exception DuplicateVar of string
exception UnboundVar of string

type denv (** bound variables *)

val denv_add_var : denv -> preid -> dty -> denv

val denv_add_let : denv -> dterm -> preid -> denv

val denv_add_quant : denv -> (preid * dty) list -> denv

val denv_add_pat : denv -> dpattern -> denv

val denv_get_var : ?loc:Loc.position -> denv -> string -> dterm

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dterm : ?loc:Loc.position -> dterm_node -> dterm

val dterm_type_cast : dterm -> ty -> dterm

val dterm_add_label : dterm -> label -> dterm

val dterm_set_labels : dterm -> Slab.t -> dterm

val dterm_set_uloc : dterm -> Loc.position -> dterm

(** Final stage *)

val term : strict:bool -> keep_loc:bool -> vsymbol Mstr.t -> dterm -> term

