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

open Ident
open Ty
open Term

(** {2 Individual types (first-order types without effects)} *)

type itysymbol = private {
  its_ts      : tysymbol;       (** pure "snapshot" type symbol *)
  its_privmut : bool;           (** private mutable record type *)
  its_mfields : pvsymbol list;  (** mutable record fields *)
  its_regions : region list;    (** mutable shareable components *)
  its_arg_imm : bool list;      (** non-updatable type parameters *)
  its_arg_exp : bool list;      (** exposed type parameters *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_frz : bool list;      (** irreplaceable type parameters *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_reg_frz : bool list;      (** irreplaceable shareable components *)
  its_def     : ity type_def;   (** type definition *)
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

exception ImpureField of ity
exception DuplicateRegion of region
exception UnboundRegion of region

(** creation of a symbol for type in programs *)

val create_itysymbol_pure : preid -> tvsymbol list -> itysymbol
(** [create_itysymbol_pure id args] creates a new type symbol with
    immutable type arguments and with no mutable fields or subregions.
    This function should be used for all immutable non-updatable types:
    abstract types, private immutable records, immutable records with
    invariant, and recursive algebraic types. *)

val create_itysymbol_alias : preid -> tvsymbol list -> ity -> itysymbol
(** [create_itysymbol_alias id args def] creates a new type alias. *)

val create_itysymbol_rich :
  preid -> tvsymbol list -> bool -> bool Mpv.t -> itysymbol
(** [create_itysymbol_rich id args privmut fields] creates a new type symbol.
    Each field is represented by a [pvsymbol] mapped to its mutability status
    in [fields]. The variables corresponding to mutable fields are stored in
    the created type symbol and used in effects. If [privmut] is [true],
    then all types in [fields] must be pure. *)

val restore_its : tysymbol -> itysymbol
(** raises [Not_found] if the argument is not a [its_ts] *)

val its_mutable : itysymbol -> bool
(** [its_mutable s] checks if [s] is a mutable record or an alias for one *)

val its_impure : itysymbol -> bool
(** [its_impure s] checks if [s] is mutable or has mutable components *)

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

exception IllegalAlias of region
exception AssignPrivate of region
exception StaleVariable of pvsymbol * region
exception BadGhostWrite of pvsymbol * region
exception DuplicateField of region * pvsymbol
exception GhostDivergence

type effect = private {
  eff_reads  : Spv.t;         (* known variables *)
  eff_writes : Spv.t Mreg.t;  (* modifications to specific fields *)
  eff_covers : Sreg.t Mreg.t; (* confinement of regions to covers *)
  eff_taints : Sreg.t;        (* ghost modifications *)
  eff_raises : Sexn.t;        (* raised exceptions *)
  eff_oneway : bool;          (* non-termination *)
  eff_ghost  : bool;          (* ghost status *)
}

val eff_empty : effect

val eff_equal : effect -> effect -> bool
val eff_pure : effect -> bool

val eff_read : Spv.t -> effect
val eff_write : Spv.t -> Spv.t Mreg.t -> effect (* drops writes outside reads *)
val eff_assign : (pvsymbol * pvsymbol * pvsymbol) list -> effect (* r,field,v *)

val eff_read_pre  : Spv.t -> effect -> effect (* no stale-variable check *)
val eff_read_post : effect -> Spv.t -> effect (* checks for stale variables *)
val eff_bind      : Spv.t -> effect -> effect (* removes variables from reads *)

val eff_read_single      : pvsymbol -> effect
val eff_read_single_pre  : pvsymbol -> effect -> effect
val eff_read_single_post : effect -> pvsymbol -> effect
val eff_bind_single      : pvsymbol -> effect -> effect

val eff_reset : effect -> region -> effect  (* confine to an empty cover *)
val eff_strong : effect -> effect (* confine all subregions under writes *)

val eff_raise : effect -> xsymbol -> effect
val eff_catch : effect -> xsymbol -> effect

val eff_diverge : effect -> effect            (* forbidden if ghost *)
val eff_ghostify : bool -> effect -> effect   (* forbidden if diverges *)

val eff_contagious : effect -> bool           (* ghost and raising exceptions *)

val eff_union_seq : effect -> effect -> effect  (* checks for stale variables *)
val eff_union_par : effect -> effect -> effect  (* no stale-variable check *)

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
  cty_oldies : pvsymbol Mpv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_freeze : ity_subst;
}

val create_cty : pvsymbol list ->
  pre list -> post list -> post list Mexn.t ->
  pvsymbol Mpv.t -> effect -> ity -> cty
(** [create_cty args pre post xpost oldies effect result] creates a cty.
    The [cty_xpost] field does not have to cover all raised exceptions.
    [cty_effect.eff_reads] is completed wrt the specification and [args].
    [cty_freeze] freezes every unbound pvsymbol in [cty_effect.eff_reads].
    All effects on regions outside [cty_effect.eff_reads] are removed.
    Fresh regions in [result] are reset. Every type variable in [pre],
    [post], and [xpost] must come from [cty_reads], [args] or [result].
    [oldies] maps ghost pure snapshots of the parameters and external
    reads to the original pvsymbols: these snaphosts are removed from
    [cty_effect.eff_reads] and replaced with the originals. *)

val cty_apply : cty -> pvsymbol list -> ity list -> ity -> cty
(** [cty_apply cty pvl rest res] instantiates [cty] up to the types in
    [pvl], [rest], and [res], then applies it to the arguments in [pvl],
    and returns the computation type of the result, [rest -> res],
    with every type variable and region in [pvl] being frozen. *)

val cty_ghost : cty -> bool
(** [cty_ghost cty] returns [cty.cty_effect.eff_ghost] *)

val cty_ghostify : bool -> cty -> cty
(** [cty_ghostify ghost cty] ghostifies the effect of [cty]. *)

val cty_reads : cty -> Spv.t
(** [cty_reads cty] returns the set of external dependencies of [cty]. *)

val cty_add_reads : cty -> Spv.t -> cty
(** [cty_add_reads cty pvs] adds [pvs] to [cty.cty_effect.eff_reads].
    This function performs capture: if some variables in [pvs] occur
    in [cty.cty_args], they are not frozen. *)

val cty_add_pre : pre list -> cty -> cty
(** [cty_add_pre fl cty] appends pre-conditions in [fl] to [cty.cty_pre].
    This function performs capture: the formulas in [fl] may refer to
    the variables in [cty.cty_args]. Only the new external dependencies
    in [fl] are added to [cty.cty_effect.eff_reads] and frozen. *)

val cty_add_post : cty -> post list -> cty
(** [cty_add_post cty fl] appends post-conditions in [fl] to [cty.cty_post].
    This function performs capture: the formulas in [fl] may refer to the
    variables in [cty.cty_args]. Only the new external dependencies in [fl]
    are added to [cty.cty_effect.eff_reads] and frozen. *)

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

val print_spec :
  pvsymbol list -> pre list -> post list -> post list Mexn.t ->
    effect -> Format.formatter -> ity option -> unit (* piecemeal cty *)
