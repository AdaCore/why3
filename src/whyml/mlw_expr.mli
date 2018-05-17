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

(** {1 Program Expressions} *)

open Wstdlib
open Ident
open Term
open Mlw_ty
open Mlw_ty.T


(** {2 Program/logic symbols} *)

(** {!plsymbol}s represent algebraic type constructors and projections.
   They must be fully applied and the result is equal to the application of
   the lsymbol. We need this kind of symbols to cover nullary constructors,
   such as [Nil], which cannot be given a post-condition. They cannot be
   locally defined and therefore every type variable and region in their
   type signature can be instantiated. *)

type field = {
  fd_ity   : ity;
  fd_ghost : bool;
  fd_mut   : region option;
}

type plsymbol = private {
  pl_ls     : lsymbol;
  pl_args   : field list;
  pl_value  : field;
  pl_hidden : bool;
  pl_rdonly : bool;
}

val pl_equal : plsymbol -> plsymbol -> bool

val create_plsymbol :
  ?hidden:bool -> ?rdonly:bool -> ?constr:int ->
    preid -> field list -> field -> plsymbol

val restore_pl : lsymbol -> plsymbol
(** raises [Not_found] if the argument is not a [pl_ls] *)

exception HiddenPLS of plsymbol
exception RdOnlyPLS of plsymbol

(** {2 Cloning} *)

type symbol_map = private {
  sm_pure : Theory.symbol_map;
  sm_its  : itysymbol Mits.t;
  sm_pls  : plsymbol Mls.t;
}

val pl_clone : Theory.symbol_map -> symbol_map

(** {2 Patterns} *)

type ppattern = private {
  ppat_pattern : pattern;
  ppat_ity     : ity;
  ppat_ghost   : bool;  (* matches a ghost value *)
  ppat_fail    : bool;  (* refutable under ghost *)
}

type pre_ppattern =
  | PPwild
  | PPvar  of preid
  | PPlapp of lsymbol * pre_ppattern list
  | PPpapp of plsymbol * pre_ppattern list
  | PPor   of pre_ppattern * pre_ppattern
  | PPas   of pre_ppattern * preid

val make_ppattern :
  pre_ppattern -> ?ghost:bool -> ity -> pvsymbol Mstr.t * ppattern

(** {2 Program symbols} *)

(** {!psymbol}s represent lambda-abstractions. They are polymorphic and
   can be type-instantiated in some type variables and regions of
   their type signature. *)

type psymbol = private {
  ps_name  : ident;
  ps_aty   : aty;
  ps_ghost : bool;
  ps_pvset : Spv.t;
  ps_vars  : varset;
  (** this varset covers the type variables and regions of the defining
     lambda that cannot be instantiated. Every other type variable
     and region in [ps_aty] is generalized and can be instantiated. *)
  ps_subst : ity_subst;
  (** this substitution instantiates every type variable and region
     in [ps_vars] to itself *)
}

module Mps : Extmap.S with type key = psymbol
module Sps : Extset.S with module M = Mps
module Hps : Exthtbl.S with type key = psymbol
module Wps : Weakhtbl.S with type key = psymbol

val ps_equal : psymbol -> psymbol -> bool

val create_psymbol : preid -> ?ghost:bool -> aty -> psymbol

(** {2 Program expressions} *)

type assertion_kind = Aassert | Aassume | Acheck

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type let_sym =
  | LetV of pvsymbol
  | LetA of psymbol

type symset = private {
  syms_pv : Spv.t;
  syms_ps : Sps.t;
}

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_ghost  : bool;
  e_effect : effect;
  e_syms   : symset;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Elogic  of term
  | Evalue  of pvsymbol
  | Earrow  of psymbol
  | Eapp    of expr * pvsymbol * spec
  | Elet    of let_defn * expr
  | Erec    of fun_defn list * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (ppattern * expr) list
  | Eassign of plsymbol * expr * region * pvsymbol
  | Eghost  of expr
  | Eany    of spec
  | Eloop   of invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
  | Eraise  of xsymbol * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eabstr  of expr * spec
  | Eassert of assertion_kind * term
  | Eabsurd

and let_defn = private {
  let_sym  : let_sym;
  let_expr : expr;
}

and fun_defn = private {
  fun_ps     : psymbol;
  fun_lambda : lambda;
  fun_syms   : symset;
}

and lambda = {
  l_args : pvsymbol list;
  l_expr : expr;
  l_spec : spec;
}

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

val e_value : pvsymbol -> expr

val e_arrow : psymbol -> ity list -> ity -> expr
(** [e_arrow p argl res] instantiates the program function symbol [p]
    into a program expression having the given types of the arguments
    and the result. The resulting expression can be applied to
    arguments using {!e_app} given below.

    See also [examples/use_api/mlw.ml] *)

exception ValueExpected of expr
exception ArrowExpected of expr

val ity_of_expr : expr -> ity
val aty_of_expr : expr -> aty

val e_app : expr -> expr list -> expr
(** [e_app e el] builds the application of [e] to arguments [el].
    [e] is typically constructed using {!e_arrow} defined above.

    See also [examples/use_api/mlw.ml] *)

val e_lapp : lsymbol -> expr list -> ity -> expr
val e_plapp : plsymbol -> expr list -> ity -> expr

val create_let_defn    : preid -> expr -> let_defn
val create_let_pv_defn : preid -> expr -> let_defn * pvsymbol
val create_let_ps_defn : preid -> expr -> let_defn * psymbol

val create_fun_defn : preid -> lambda -> fun_defn
val create_rec_defn : (psymbol * lambda) list -> fun_defn list

exception StaleRegion of expr * ident
(** freshness violation: a previously reset region is associated to an ident *)

val e_let : let_defn -> expr -> expr
val e_rec : fun_defn list -> expr -> expr

val e_if : expr -> expr -> expr -> expr
val e_case : expr -> (ppattern * expr) list -> expr

exception Immutable of expr

val e_assign : plsymbol -> expr -> expr -> expr
val e_ghost : expr -> expr

val fs_void : lsymbol
val t_void : term
val e_void : expr

val e_const : Number.constant -> ity -> expr
val e_lazy_and : expr -> expr -> expr
val e_lazy_or : expr -> expr -> expr
val e_not : expr -> expr
val e_true : expr
val e_false : expr

val e_raise : xsymbol -> expr -> ity -> expr
val e_try : expr -> (xsymbol * pvsymbol * expr) list -> expr

val e_loop : invariant -> variant list -> expr -> expr

val e_for :
  pvsymbol -> expr -> for_direction -> expr -> invariant -> expr -> expr

val e_abstract : expr -> spec -> expr
val e_any : spec option -> vty -> expr

val e_assert : assertion_kind -> term -> expr
val e_absurd : ity -> expr

(** {2 Expression traversal} *)

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

val e_find : (expr -> bool) -> expr -> expr
(** [e_find pr e] returns a sub-expression of [e] satisfying [pr].
    raises [Not_found] if no sub-expression satisfies [pr]. *)

val e_purify : expr -> term option
