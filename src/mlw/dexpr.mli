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
open Term
open Ity
open Expr
open Pmodule

(** Program types *)

type dity

val dity_fresh : unit -> dity

val dity_of_ity : ity -> dity

val dity_int  : dity
val dity_real : dity
val dity_bool : dity
val dity_unit : dity

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)
type dref = bool list * bool

(** Patterns *)

type dpattern = private {
  dp_pat  : pre_pattern;
  dp_dity : dity;
  dp_vars : (dity * bool) Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid * bool
  | DPapp  of rsymbol * dpattern list
  | DPas   of dpattern * preid * bool
  | DPor   of dpattern * dpattern
  | DPcast of dpattern * dity

(** Binders *)

type ghost = bool

type dbinder = preid option * ghost * dity

(** Specifications *)

exception UnboundLabel of string

val old_label : string

type register_old = string -> pvsymbol -> pvsymbol
  (** Program variables occurring under [old] or [at] are passed to
      a registrar function. The label string must be ["'Old"] for [old]. *)

type 'a later = pvsymbol Mstr.t -> xsymbol Mstr.t -> register_old -> 'a
  (** Specification terms are parsed and typechecked after the program
      expressions, when the types of locally bound program variables are
      already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (pvsymbol * term) list;
  ds_xpost   : (pvsymbol * term) list Mxs.t;
  ds_reads   : pvsymbol list;
  ds_writes  : term list;
  ds_diverge : bool;
  ds_partial : bool;
  ds_checkrw : bool;
}

type dspec = ity -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

(** Expressions *)

type dinvariant = term list

type dxsymbol =
  | DElexn of string * dity
  | DEgexn of xsymbol

type dexpr = private {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty * dref
  | DEsym of prog_symbol
  | DEconst of Number.constant * dity
  | DEapp of dexpr * dexpr
  | DEfun of dbinder list * dity * mask * dspec later * dexpr
  | DEany of dbinder list * dity * mask * dspec later
  | DElet of dlet_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEnot of dexpr
  | DEand of dexpr * dexpr
  | DEor of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * dreg_branch list * dexn_branch list
  | DEassign of (dexpr * rsymbol * dexpr) list
  | DEwhile of dexpr * dinvariant later * variant list later * dexpr
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEraise of dxsymbol * dexpr
  | DEghost of dexpr
  | DEexn of preid * dity * mask * dexpr
  | DEoptexn of preid * dity * mask * dexpr
  | DEassert of assertion_kind * term later
  | DEpure of term later * dity
  | DEvar_pure of string * dvty * dref
  | DEls_pure of lsymbol * bool
  | DEpv_pure of pvsymbol
  | DEabsurd
  | DEtrue
  | DEfalse
  | DElabel of preid * dexpr
  | DEcast of dexpr * dity
  | DEuloc of dexpr * Loc.position
  | DEattr of dexpr * Sattr.t

and dreg_branch = dpattern * dexpr

and dexn_branch = dxsymbol * dpattern * dexpr

and dlet_defn = preid * ghost * rs_kind * dexpr

and drec_defn = private { fds : dfun_defn list }

and dfun_defn = preid * ghost * rs_kind * dbinder list *
  dity * mask * dspec later * variant list later * dexpr

(** Environment *)

type denv

val denv_empty : denv

val denv_add_var : denv -> preid -> dity -> denv

val denv_add_let : denv -> dlet_defn -> denv

val denv_add_args : denv -> dbinder list -> denv

val denv_add_pat : denv -> dpattern -> dity -> denv
val denv_add_expr_pat : denv -> dpattern -> dexpr -> denv
val denv_add_exn_pat : denv -> dpattern -> dxsymbol -> denv

val denv_add_for_index : denv -> preid -> dvty -> denv

val denv_add_exn : denv -> preid -> dity -> denv

val denv_get : denv -> string -> dexpr_node (** raises UnboundVar *)
val denv_get_opt : denv -> string -> dexpr_node option

val denv_get_pure : denv -> string -> dexpr_node (** raises UnboundVar *)
val denv_get_pure_opt : denv -> string -> dexpr_node option

val denv_get_exn : denv -> string -> dxsymbol (** raises Not_found *)
val denv_get_exn_opt : denv -> string -> dxsymbol option

val denv_names : denv -> Sstr.t

val denv_pure : denv -> (Dterm.denv -> Dterm.dty) -> dity

(** Constructors *)

val dpattern : ?loc:Loc.position -> dpattern_node -> dpattern

val dexpr : ?loc:Loc.position -> dexpr_node -> dexpr

type pre_fun_defn = preid * ghost * rs_kind * dbinder list *
  dity * mask * (denv -> dspec later * variant list later * dexpr)

val drec_defn : denv -> pre_fun_defn list -> denv * drec_defn

val undereference : dexpr -> dexpr
  (* raises Not_found if the argument is not auto-dereferenced *)

(** Final stage *)

val expr : ?keep_loc:bool -> ?ughost:bool -> dexpr -> expr

val let_defn : ?keep_loc:bool -> dlet_defn -> let_defn
val rec_defn : ?keep_loc:bool -> drec_defn -> let_defn
