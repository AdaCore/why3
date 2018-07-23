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

open Wstdlib
open Ident
open Ty
open Term

(** Types *)

type dty

val dty_fresh : unit -> dty

val dty_of_ty : ty -> dty

val dty_var : tvsymbol -> dty
val dty_app : tysymbol -> dty list -> dty

val dty_match : dty -> ty  -> unit (* raises Exit on failure *)
val dty_unify : dty -> dty -> unit (* raises Exit on failure *)

val dty_int  : dty
val dty_real : dty
val dty_bool : dty

val dty_fold : (tysymbol -> 'a list -> 'a) ->
               (tvsymbol -> 'a) -> (int -> 'a) -> dty -> 'a

(** Patterns, terms, and formulas *)

type dpattern = private {
  dp_node : dpattern_node;
  dp_dty  : dty;
  dp_vars : dty Mstr.t;
  dp_loc  : Loc.position option;
}

and dpattern_node =
  | DPwild
  | DPvar of preid
  | DPapp of lsymbol * dpattern list
  | DPor of dpattern * dpattern
  | DPas of dpattern * preid
  | DPcast of dpattern * dty

type dbinop =
  | DTand | DTand_asym | DTor | DTor_asym | DTimplies | DTiff | DTby | DTso

type dquant =
  | DTforall | DTexists | DTlambda

type dbinder = preid option * dty * Loc.position option

type dterm = private {
  dt_node  : dterm_node;
  dt_dty   : dty option;
  dt_loc   : Loc.position option;
}

and dterm_node =
  | DTvar of string * dty
  | DTgvar of vsymbol
  | DTconst of Number.constant * dty
  | DTapp of lsymbol * dterm list
  | DTfapp of dterm * dterm
  | DTif of dterm * dterm * dterm
  | DTlet of dterm * preid * dterm
  | DTcase of dterm * (dpattern * dterm) list
  | DTeps of preid * dty * dterm
  | DTquant of dquant * dbinder list * dterm list list * dterm
  | DTbinop of dbinop * dterm * dterm
  | DTnot of dterm
  | DTtrue
  | DTfalse
  | DTcast of dterm * dty
  | DTuloc of dterm * Loc.position
  | DTattr of dterm * Sattr.t

(** Environment *)

exception TermExpected
exception FmlaExpected
exception DuplicateVar of string
exception UnboundVar of string

type denv = dterm_node Mstr.t (** bound variables *)

val denv_empty : denv (** Mstr.empty *)

val denv_add_var : denv -> preid -> dty -> denv

val denv_add_let : denv -> dterm -> preid -> denv

val denv_add_quant : denv -> dbinder list -> denv

val denv_add_pat : denv -> dpattern -> dty -> denv
val denv_add_term_pat : denv -> dpattern -> dterm -> denv

val denv_get : denv -> string -> dterm_node (** raises UnboundVar *)

val denv_get_opt : denv -> string -> dterm_node option

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dterm : Coercion.t -> ?loc:Loc.position -> dterm_node -> dterm

(** Final stage *)

val debug_ignore_unused_var : Debug.flag
val attr_w_unused_var_no : Ident.attribute

val term : ?strict:bool -> ?keep_loc:bool -> dterm -> term

val fmla : ?strict:bool -> ?keep_loc:bool -> dterm -> term
