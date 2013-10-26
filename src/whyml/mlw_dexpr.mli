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
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** Program types *)

type dity

val dity_fresh : unit -> dity

val dity_of_ity : ity -> dity

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

val dity_is_bool : dity -> bool

val dvty_is_chainable : dvty -> bool

(** Patterns *)

type dpattern = private {
  dp_pat  : pre_ppattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPlapp of lsymbol * dpattern list
  | DPpapp of plsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid

(** Specifications *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid option * ghost * opaque * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec = {
  ds_pre     : pre;
  ds_post    : post;
  ds_xpost   : xpost;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
}

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dlazy_op = DEand | DEor

type dexpr = private {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEgpvar of pvsymbol
  | DEgpsym of psymbol
  | DEplapp of plsymbol * dexpr list
  | DElsapp of lsymbol * dexpr list
  | DEapply of dexpr * dexpr list
  | DEconst of Number.constant
  | DEval of dval_decl * dexpr
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of dfun_defn list * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * invariant later * dexpr
  | DEloop of variant list later * invariant later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_c
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dval_decl = preid * ghost * dtype_v

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dexpr * dspec later

(** Environment *)

type denv

val denv_empty : denv

val denv_add_val : denv -> dval_decl -> denv

val denv_add_let : denv -> dlet_defn -> denv

val denv_add_fun : denv -> dfun_defn -> denv

val denv_prepare_rec : denv -> (preid * dbinder list * dity) list -> denv
  (* [denv_prepare_rec] adds to the environment the user-supplied
     types of every function in a (mutually) recursive definition.
     Every user type variable not frozen in [denv] is generalized,
     and must not be unified with any outer fresh type variable. *)

val denv_verify_rec : denv -> preid -> unit
  (* after a (mutually) recursive definition has been typechecked,
     [denv_verify_rec] should be called for every function on the
     [denv] before [denv_prepare_rec]. This function verifies that
     the resulting functions are not less polymorphic than expected
     according the user-supplied type annotations. *)

val denv_add_args : denv -> dbinder list -> denv

val denv_add_pat : denv -> dpattern -> denv

val denv_get : denv -> string -> dexpr_node (** raises UnboundVar *)

val denv_get_opt : denv -> string -> dexpr_node option

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dexpr : ?loc:Loc.position -> dexpr_node -> dexpr

(** Final stage *)

val expr     : strict:bool -> keep_loc:bool -> dexpr -> expr
val val_decl : strict:bool -> keep_loc:bool -> dval_decl -> let_sym
val let_defn : strict:bool -> keep_loc:bool -> dlet_defn -> let_defn
val fun_defn : strict:bool -> keep_loc:bool -> dfun_defn -> fun_defn
val rec_defn : strict:bool -> keep_loc:bool -> dfun_defn list -> fun_defn list
