(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term

(** {2 Individual types (first-order types w/o effects)} *)

type itysymbol = private {
  its_ts      : tysymbol;       (** pure "snapshot" type symbol *)
  its_private : bool;           (** is a private/abstract type *)
  its_mutable : bool;           (** is a record with mutable fields *)
  its_mfields : pvsymbol list;  (** mutable fields of a mutable type *)
  its_ifields : pvsymbol list;  (** immutable fields of a mutable type *)
  its_regions : region list;    (** mutable shareable components *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_upd : bool list;      (** updatable type parameters *)
  its_arg_exp : bool list;      (** exposed type parameters *)
  its_def     : ity option;     (** is a type alias *)
}

and ity = private {
  ity_node : ity_node;
  ity_pure : bool;
  ity_tag  : Weakhtbl.tag;
}

and ity_node = private
  | Ityreg of region
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * region list
    (** algebraic type with shareable components *)
  | Itypur of itysymbol * ity list
    (** immutable type or a snapshot of a mutable type *)
  | Ityvar of tvsymbol
    (** type variable *)

and region = private {
  reg_name : ident;
  reg_its  : itysymbol;
  reg_args : ity list;
  reg_regs : region list;
}

and pvsymbol = private {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

module Mits : Extmap.S with type key = itysymbol
module Sits : Extset.S with module M = Mits
module Hits : Exthtbl.S with type key = itysymbol
module Wits : Weakhtbl.S with type key = itysymbol

module Mity : Extmap.S with type key = ity
module Sity : Extset.S with module M = Mity
module Hity : Exthtbl.S with type key = ity
module Wity : Weakhtbl.S with type key = ity

module Mreg : Extmap.S with type key = region
module Sreg : Extset.S with module M = Mreg
module Hreg : Exthtbl.S with type key = region
module Wreg : Weakhtbl.S with type key = region

module Mpv  : Extmap.S with type key = pvsymbol
module Spv  : Extset.S with module M = Mpv
module Hpv  : Exthtbl.S with type key = pvsymbol
module Wpv  : Weakhtbl.S with type key = pvsymbol

val its_compare : itysymbol -> itysymbol -> int
val ity_compare : ity -> ity -> int
val reg_compare : region -> region -> int
val pv_compare  : pvsymbol -> pvsymbol -> int

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool
val reg_equal : region -> region -> bool
val pv_equal  : pvsymbol -> pvsymbol -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int
val reg_hash : region -> int
val pv_hash  : pvsymbol -> int

exception DuplicateRegion of region
exception UnboundRegion of region

(** creation of a symbol for type in programs *)
val create_itysymbol :
  preid -> (tvsymbol * bool * bool * bool) list ->
    bool -> bool -> (region * bool) list ->
    bool Mpv.t -> ity option -> itysymbol

val restore_its : tysymbol -> itysymbol
(** raises [Not_found] if the argument is not a [its_ts] *)

(** {2 Type constructors} *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int
exception NonUpdatable of itysymbol * ity

val create_region : preid -> itysymbol -> ity list -> region list -> region
(** the type symbol must be mutable, aliases are allowed *)

val ity_reg : region -> ity
val ity_var : tvsymbol -> ity

val ity_pur : itysymbol -> ity list -> ity
(** [ity_pur] may be applied to mutable type symbols to create a snapshot *)

val ity_app : itysymbol -> ity list -> region list -> ity
(** [ity_app s tl rl] creates
  - a fresh region and an [Ityreg] type if [s] is mutable
  - an [Itypur] type if [s] is not mutable and [rl] is empty
  - an [Ityapp] type otherwise *)

val ity_app_fresh : itysymbol -> ity list -> ity
(** [ity_app_fresh] creates fresh regions where needed *)

val ty_of_ity : ity -> ty
(** all aliases expanded, all regions removed *)

val ity_of_ty : ty -> ity
(** snapshot type, raises [Invalid_argument] for any non-its *)

val ity_purify : ity -> ity
(** snapshot type *)

(** {2 Generic traversal functions} *)

val ity_fold : ('a -> ity -> 'a) -> ('a -> region -> 'a) -> 'a -> ity -> 'a
val reg_fold : ('a -> ity -> 'a) -> ('a -> region -> 'a) -> 'a -> region -> 'a

(** {2 Traversal functions on type symbols} *)

val ity_s_fold : ('a -> itysymbol -> 'a) -> 'a -> ity -> 'a
val reg_s_fold : ('a -> itysymbol -> 'a) -> 'a -> region -> 'a

(** {2 Traversal functions on type variables} *)

val ity_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> ity -> 'a
val reg_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> region -> 'a

(** {2 Traversal functions on top regions} *)

val ity_r_fold : ('a -> region -> 'a) -> 'a -> ity -> 'a
val reg_r_fold : ('a -> region -> 'a) -> 'a -> region -> 'a

(** {2 Miscellaneous type utilities} *)

val ity_freevars : Stv.t -> ity -> Stv.t
val reg_freevars : Stv.t -> region -> Stv.t

val ity_v_occurs : tvsymbol -> ity -> bool
val reg_v_occurs : tvsymbol -> region -> bool

val ity_r_occurs : region -> ity -> bool
val reg_r_occurs : region -> region -> bool

val ity_r_stale  : region -> Sreg.t -> ity -> bool
val reg_r_stale  : region -> Sreg.t -> region -> bool

val ity_closed    : ity -> bool
val ity_immutable : ity -> bool

(* detect non-ghost type variables and regions *)

val ity_r_visible : Sreg.t -> ity -> Sreg.t
val ity_v_visible : Stv.t  -> ity -> Stv.t

(** {2 Built-in types} *)

val ts_unit : tysymbol (** the same as [Ty.ts_tuple 0] *)
val ty_unit : ty

val its_int  : itysymbol
val its_real : itysymbol
val its_bool : itysymbol
val its_unit : itysymbol
val its_func : itysymbol
val its_pred : itysymbol

val ity_int  : ity
val ity_real : ity
val ity_bool : ity
val ity_unit : ity
val ity_func : ity -> ity -> ity
val ity_pred : ity -> ity (* ity_pred 'a == ity_func 'a ity_bool *)

val its_tuple : int -> itysymbol
val ity_tuple : ity list -> ity

(** {2 Type matching and instantiation} *)

type ity_subst = private {
  isb_tv  : ity Mtv.t;
  isb_reg : region Mreg.t;
}

exception TypeMismatch of ity * ity * ity_subst

val isb_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst
val reg_match : ity_subst -> region -> region -> ity_subst

val ity_freeze : ity_subst -> ity -> ity_subst (* self-match *)
val reg_freeze : ity_subst -> region -> ity_subst (* self-match *)

val ity_equal_check : ity -> ity -> unit
val reg_equal_check : region -> region -> unit

val ity_full_inst : ity_subst -> ity -> ity
val reg_full_inst : ity_subst -> region -> region

(** {2 Program variables} *)

val create_pvsymbol : preid -> ?ghost:bool -> ity -> pvsymbol

val restore_pv : vsymbol -> pvsymbol
(** raises [Not_found] if the argument is not a [pv_vs] *)

val t_freepvs : Spv.t -> term -> Spv.t
(** raises [Not_found] if the term contains a free variable
    which is not a [pv_vs] *)

val pvs_of_vss : Spv.t -> Svs.t -> Spv.t

(** {2 Exception symbols} *)

type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (** closed and immutable *)
}

module Mexn : Extmap.S with type key = xsymbol
module Sexn : Extset.S with module M = Mexn

val xs_compare : xsymbol -> xsymbol -> int
val xs_equal : xsymbol -> xsymbol -> bool
val xs_hash: xsymbol -> int

val create_xsymbol : preid -> ity -> xsymbol

(** {2 Effects} *)

type effect = private {
  eff_writes : Spv.t Mreg.t;
  eff_resets : Sreg.t Mreg.t;
  eff_raises : Sexn.t;
  eff_diverg : bool;
}

val eff_empty : effect
val eff_equal : effect -> effect -> bool
val eff_union : effect -> effect -> effect

val eff_is_empty : effect -> bool
val eff_is_pure  : effect -> bool

exception AssignPrivate of region
exception DuplicateField of region * pvsymbol
exception WriteImmutable of region * pvsymbol

val eff_write : effect -> region -> Spv.t -> effect
val eff_raise : effect -> xsymbol -> effect
val eff_catch : effect -> xsymbol -> effect
val eff_reset : effect -> region -> effect

val eff_diverge : effect -> effect

val eff_assign : effect -> (region * pvsymbol * ity) list -> effect

val refresh_of_effect : effect -> effect

exception IllegalAlias of region

val eff_full_inst : ity_subst -> effect -> effect

val eff_stale_region : effect -> ity -> bool

(** {2 Computation types (higher-order types with effects)} *)

type pre = term   (** precondition: pre_fmla *)
type post = term  (** postcondition: eps result . post_fmla *)

val create_post : vsymbol -> term -> post
val open_post : post -> vsymbol * term

type cty = private {
  cty_args   : pvsymbol list;
  cty_pre    : pre list;
  cty_post   : post list;
  cty_xpost  : post list Mexn.t;
  cty_reads  : Spv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_freeze : ity_subst;
}

val create_cty : pvsymbol list ->
  pre list -> post list -> post list Mexn.t -> Spv.t -> effect -> ity -> cty
(** [create_cty args pre post xpost reads effect result] creates a cty.
    The [cty_xpost] field does not have to cover all raised exceptions.
    The [cty_reads] field contains all unbound variables from the spec.
    The [cty_freeze] field freezes every pvsymbol in [cty_reads].
    The [cty_effect] field is filtered wrt [cty_reads] and [args].
    Fresh regions in [result] are reset. Every type variable in [pre],
    [post], and [xpost] must come from [cty_reads], [args] or [result]. *)

val cty_apply :
  ?ghost:bool -> cty -> pvsymbol list -> ity list -> ity -> bool * cty
(** [cty_apply ?(ghost=false) cty pvl rest res] instantiates [cty]
    up to the types in [pvl], [rest] and [res], then applies it to
    the arguments in [pvl], and returns the ghost status and the
    computation type of the result, [rest -> res], with every type
    variable and region in [pvl] freezed. Typecasts into a mapping
    type are allowed for total effectless computations. *)

val cty_r_visible : cty -> Sreg.t
(** [cty_r_visible cty] returns the set of regions which are visible
    from the non-ghost read dependencies and arguments of [cty]. *)

val cty_ghost_writes : bool -> cty -> Spv.t Mreg.t
(** [cty_ghost_writes ghost cty] returns the subset of the write effect
    of [cty] which corresponds to ghost writes into visible fields of
    the ghost read dependencies and arguments of [cty]. *)

val cty_add_reads : cty -> Spv.t -> cty
(** [cty_add_reads cty pvs] adds variables in [pvs] to [cty.cty_reads].
    This function performs capture: if some variables in [pvs] occur in
    [cty.cty_args], they are removed from [pvs], and the corresponding
    type variables and regions are not frozen. *)

val cty_add_pre : cty -> pre list -> cty
(** [cty_add_pre cty fl] appends pre-conditions in [fl] to [cty.cty_pre].
    This function performs capture: the formulas in [fl] may refer to
    the variables in [cty.cty_args]. Only the new external dependencies
    in [fl] are added to [cty.cty_reads] and frozen. *)

val cty_add_post : cty -> post list -> cty
(** [cty_add_post cty fl] appends post-conditions in [fl] to [cty.cty_post].
    This function performs capture: the formulas in [fl] may refer to the
    variables in [cty.cty_args]. Only the new external dependencies in [fl]
    are added to [cty.cty_reads] and frozen. *)

(** {2 Pretty-printing} *)

val forget_reg : region -> unit   (* flush id_unique for a region *)
val forget_pv  : pvsymbol -> unit (* flush for a program variable *)

val print_its : Format.formatter -> itysymbol -> unit (* type symbol *)
val print_reg : Format.formatter -> region -> unit    (* region *)
val print_ity : Format.formatter -> ity -> unit       (* individual type *)
val print_ity_full : Format.formatter -> ity -> unit  (* type with regions *)

val print_xs   : Format.formatter -> xsymbol -> unit  (* exception symbol *)
val print_pv   : Format.formatter -> pvsymbol -> unit (* program variable *)
val print_pvty : Format.formatter -> pvsymbol -> unit (* pvsymbol : type *)
val print_cty  : Format.formatter -> cty -> unit      (* computation type *)

val print_spec : pvsymbol list -> pre list -> post list -> post list Mexn.t ->
  Spv.t -> effect -> Format.formatter -> ity option -> unit (* piecemeal cty *)
