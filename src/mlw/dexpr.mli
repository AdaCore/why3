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
open Ity
open Expr

(** Program types *)

type dity

val dity_fresh : unit -> dity

val dity_of_ity : ity -> dity

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

val dity_is_bool : dity -> bool

val dvty_is_chainable : dvty -> bool

(** Patterns *)

type dpattern = private {
  dp_pat  : pre_pattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPapp  of rsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid
  | DPcast of dpattern * ity

(** Binders *)

type ghost = bool

type dbinder = preid option * ghost * dity

(** Specifications *)

exception UnboundLabel of string

type register_old = pvsymbol -> string -> pvsymbol
  (** Program variables occurring under [old] or [at] are passed to
      a registrar function. The label string must be ['0] for [old]. *)

type 'a later = pvsymbol Mstr.t -> register_old -> 'a
  (** Specification terms are parsed and typechecked after the program
      expressions, when the types of locally bound program variables are
      already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (vsymbol option * term) list;
  ds_xpost   : (vsymbol option * term) list Mexn.t;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_diverge : bool;
  ds_checkrw : bool;
}

type dspec = ty -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

(** Expressions *)

type dinvariant = term list

type dexpr = private {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEpv of pvsymbol
  | DErs of rsymbol
  | DEconst of Number.constant
  | DEapp of dexpr * dexpr
  | DEfun of dbinder list * dspec later * dexpr
  | DEany of dbinder list * dspec later * dity
  | DElet of dlet_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEnot of dexpr
  | DEand of dexpr * dexpr
  | DEor of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEcase of dexpr * (dpattern * dexpr) list
  | DEassign of (dexpr * rsymbol * dexpr) list
  | DEwhile of dexpr * dinvariant later * variant list later * dexpr
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEraise of xsymbol * dexpr
  | DEghost of dexpr
  | DEassert of assertion_kind * term later
  | DEpure of term later
  | DEabsurd
  | DEtrue
  | DEfalse
  | DEmark of preid * dexpr
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dlet_defn = preid * ghost * rs_kind * dexpr

and drec_defn = private { fds : dfun_defn list }

and dfun_defn = preid * ghost * rs_kind *
  dbinder list * dspec later * variant list later * dexpr

(** Environment *)

type denv

val denv_empty : denv

val denv_add_var : denv -> preid -> dity -> denv

val denv_add_let : denv -> dlet_defn -> denv

val denv_add_args : denv -> dbinder list -> denv

val denv_add_pat : denv -> dpattern -> denv

val denv_get : denv -> string -> dexpr_node (** raises UnboundVar *)

val denv_get_opt : denv -> string -> dexpr_node option

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dexpr : ?loc:Loc.position -> dexpr_node -> dexpr

type pre_fun_defn = preid * ghost * rs_kind * dbinder list *
  dity * (denv -> dspec later * variant list later * dexpr)

val drec_defn : denv -> pre_fun_defn list -> denv * drec_defn

(** Final stage *)

val expr : ?keep_loc:bool -> dexpr -> expr

val let_defn : ?keep_loc:bool -> dlet_defn -> let_defn
val rec_defn : ?keep_loc:bool -> drec_defn -> let_defn
