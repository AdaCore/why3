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
  | DPcast of dpattern * ity

(** Binders *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid option * ghost * opaque * dity

(** Specifications *)

type 'a later = vsymbol Mstr.t -> 'a
  (* Specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (vsymbol option * term) list;
  ds_xpost   : (vsymbol option * term) list Mexn.t;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
  ds_checkrw : bool;
  ds_diverge : bool;
}

type dspec = ty -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dinvariant = term list

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
  | DEapply of dexpr * dexpr
  | DEconst of Number.constant * ity
  | DElam of dbinder list * dexpr * dspec later
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEcase of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEwhile of dexpr * (variant list * dinvariant) later * dexpr
  | DEloop of (variant list * dinvariant) later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_v * dspec later option
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dexpr * dspec later

and drec_defn = private { fds : dfun_defn list }

type dval_decl = preid * ghost * dtype_v

(** Environment *)

type denv

val denv_empty : denv

val denv_add_var : denv -> preid -> dity -> denv

val denv_add_let : denv -> dlet_defn -> denv

val denv_add_fun : denv -> dfun_defn -> denv

val denv_add_args : denv -> dbinder list -> denv

val denv_add_pat : denv -> dpattern -> denv

val denv_get : denv -> string -> dexpr_node (** raises UnboundVar *)

val denv_get_opt : denv -> string -> dexpr_node option

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dexpr : ?loc:Loc.position -> dexpr_node -> dexpr

type pre_fun_defn =
  preid * ghost * dbinder list * dity * (denv -> dexpr * dspec later)

val drec_defn : denv -> pre_fun_defn list -> denv * drec_defn

(** Final stage *)

val expr : keep_loc:bool ->
  Decl.known_map -> Mlw_decl.known_map -> dexpr -> expr

val let_defn : keep_loc:bool ->
  Decl.known_map -> Mlw_decl.known_map -> dlet_defn -> let_defn

val fun_defn : keep_loc:bool ->
  Decl.known_map -> Mlw_decl.known_map -> dfun_defn -> fun_defn

val rec_defn : keep_loc:bool ->
  Decl.known_map -> Mlw_decl.known_map -> drec_defn -> fun_defn list

val val_decl : keep_loc:bool ->
  Decl.known_map -> Mlw_decl.known_map -> dval_decl -> let_sym
