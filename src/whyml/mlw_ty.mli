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

(** {1 Program Types} *)

open Ident
open Ty
open Term

(** {2 Individual types (first-order types w/o effects)} *)

module rec T : sig

  type varset = private {
    vars_tv  : Stv.t;
    vars_reg : Sreg.t;
  }

  type itysymbol = private {
    its_ts   : tysymbol;      (** "pure snapshot" type symbol *)
    its_regs : region list;   (** region arguments *)
    its_def  : ity option;    (** type alias definition *)
    its_ghrl : bool list;     (** ghost region arguments *)
    its_inv  : bool;          (** carries a type invariant *)
    its_abst : bool;          (** is an abstract (= "model") type *)
    its_priv : bool;          (** is a private (à la Ocaml) type *)
  }

  (** ity = individual type in programs, first-order, i.e. no functions *)
  and ity = private {
    ity_node : ity_node;
    ity_vars : varset;
    ity_tag  : Weakhtbl.tag;
  }

  and ity_node = private
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = private {
    reg_name : ident;
    reg_ity  : ity;
  }

end
and Mreg : sig include Extmap.S with type key = T.region end
and Sreg : sig include Extset.S with module M = Mreg end

open T

module Mits : Extmap.S with type key = itysymbol
module Sits : Extset.S with module M = Mits
module Hits : Exthtbl.S with type key = itysymbol
module Wits : Weakhtbl.S with type key = itysymbol

module Mity : Extmap.S with type key = ity
module Sity : Extset.S with module M = Mity
module Hity : Exthtbl.S with type key = ity
module Wity : Weakhtbl.S with type key = ity

module Hreg : Exthtbl.S with type key = region
module Wreg : Weakhtbl.S with type key = region

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int

val reg_equal : region -> region -> bool
val reg_hash : region -> int

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int
exception DuplicateRegion of region
exception UnboundRegion of region

val create_region : preid -> ity -> region

(** creation of a symbol for type in programs *)
val create_itysymbol :
  preid ->
    ?abst:bool -> ?priv:bool -> ?inv:bool -> ?ghost_reg:Sreg.t ->
    tvsymbol list -> region list -> ity option -> itysymbol

val restore_its : tysymbol -> itysymbol
  (** raises [Not_found] if the argument is not a its_ts *)

val ity_var : tvsymbol -> ity
val ity_pur : tysymbol -> ity list -> ity

val ity_app : itysymbol -> ity list -> region list -> ity
val ity_app_fresh : itysymbol -> ity list -> ity

val ty_of_ity : ity -> ty
(** all aliases expanded, all regions removed *)

val ity_of_ty : ty -> ity
(** replaces every [Tyapp] with [Itypur] *)

(** {2 Generic traversal functions} *)

val ity_map : (ity -> ity) -> ity -> ity
val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val ity_all : (ity -> bool) -> ity -> bool
val ity_any : (ity -> bool) -> ity -> bool

(** {2 Traversal functions on type symbols} *)

val ity_s_fold :
  ('a -> itysymbol -> 'a) -> ('a -> tysymbol -> 'a) -> 'a -> ity -> 'a

val ity_s_all : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool
val ity_s_any : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool

val its_clone : Theory.symbol_map -> itysymbol Mits.t * region Mreg.t

val ity_closed    : ity -> bool
val ity_immutable : ity -> bool
val ity_has_inv   : ity -> bool

(* these functions attend the sub-regions *)

val reg_fold : (region -> 'a -> 'a) -> varset -> 'a -> 'a
val reg_any  : (region -> bool) -> varset -> bool
val reg_all  : (region -> bool) -> varset -> bool
val reg_iter : (region -> unit) -> varset -> unit

val reg_occurs : region -> varset -> bool

(* detect non-ghost regions *)

val ity_nonghost_reg : Sreg.t -> ity -> Sreg.t
val lookup_nonghost_reg : Sreg.t -> ity -> bool

(** {2 Built-in types} *)

val ts_unit : tysymbol (** the same as [Ty.ts_tuple 0] *)
val ty_unit : ty

val ity_int  : ity
val ity_real : ity
val ity_bool : ity
val ity_unit : ity

type ity_subst = private {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t;
}

exception RegionMismatch of region * region * ity_subst
exception TypeMismatch of ity * ity * ity_subst

val ity_subst_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst

val reg_match : ity_subst -> region -> region -> ity_subst

val ity_equal_check : ity -> ity -> unit

val reg_equal_check : region -> region -> unit

val ity_full_inst : ity_subst -> ity -> ity

val reg_full_inst : ity_subst -> region -> region

(** {2 Varset manipulation} *)

val vars_empty : varset

val vars_union : varset -> varset -> varset

val vars_freeze : varset -> ity_subst

(** {2 Exception symbols} *)

type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (** closed and immutable *)
}

val xs_equal : xsymbol -> xsymbol -> bool

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

val create_xsymbol : preid -> ity -> xsymbol

module Mexn: Extmap.S with type key = xsymbol
module Sexn: Extset.S with module M = Mexn

(** {2 Effects} *)

type effect = private {
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostw : Sreg.t; (** ghost writes *)
  eff_ghostx : Sexn.t; (** ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
  eff_compar : Stv.t;
  eff_diverg : bool;
}

val eff_empty : effect
val eff_equal : effect -> effect -> bool
val eff_union : effect -> effect -> effect
val eff_ghostify : bool -> effect -> effect

val eff_write : effect -> ?ghost:bool -> region -> effect
val eff_raise : effect -> ?ghost:bool -> xsymbol -> effect
val eff_reset : effect -> region -> effect

val eff_refresh : effect -> region -> region -> effect
val eff_assign : effect -> ?ghost:bool -> region -> ity -> effect

val eff_compare : effect -> tvsymbol -> effect
val eff_diverge : effect -> effect

val eff_remove_raise : effect -> xsymbol -> effect

val eff_stale_region : effect -> varset -> bool

exception IllegalAlias of region
exception IllegalCompar of tvsymbol * ity
exception GhostDiverg

val eff_full_inst : ity_subst -> effect -> effect

val eff_is_empty : effect -> bool

(** {2 Specification} *)

type pre = term          (** precondition: pre_fmla *)
type post = term         (** postcondition: eps result . post_fmla *)
type xpost = post Mexn.t (** exceptional postconditions *)

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

val create_post : vsymbol -> term -> post
val open_post : post -> vsymbol * term
val check_post : ty -> post -> unit

type spec = {
  c_pre     : pre;
  c_post    : post;
  c_xpost   : xpost;
  c_effect  : effect;
  c_variant : variant list;
  c_letrec  : int;
}

(** {2 Program variables} *)

type pvsymbol = private {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

module Mpv : Extmap.S with type key = pvsymbol
module Spv : Extset.S with module M = Mpv
module Hpv : Exthtbl.S with type key = pvsymbol
module Wpv : Weakhtbl.S with type key = pvsymbol

val pv_equal : pvsymbol -> pvsymbol -> bool

val create_pvsymbol : preid -> ?ghost:bool -> ity -> pvsymbol

val restore_pv : vsymbol -> pvsymbol
(** raises [Not_found] if the argument is not a [pv_vs] *)

val t_pvset : Spv.t -> term -> Spv.t
(** raises [Not_found] if the term contains non-pv variables *)

val spec_pvset : Spv.t -> spec -> Spv.t
(** raises [Not_found] if the spec contains non-pv variables *)

(** {2 Program types} *)

type vty =
  | VTvalue of ity
  | VTarrow of aty

and aty = private {
  aty_args   : pvsymbol list;
  aty_result : vty;
  aty_spec   : spec;
}

exception UnboundException of xsymbol
(** every raised exception must have a postcondition in [spec.c_xpost] *)

val vty_arrow : pvsymbol list -> ?spec:spec -> vty -> aty

val aty_pvset : aty -> Spv.t
(** raises [Not_found] if the spec contains non-pv variables *)

val aty_vars_match : ity_subst -> aty -> ity list -> ity -> ity_subst
(** this only compares the types of arguments and results, and ignores
    the spec. In other words, only the type variables and regions in
    [aty_vars aty] are matched. The caller should supply a "freezing"
    substitution that covers all external type variables and regions. *)

val aty_full_inst : ity_subst -> aty -> aty
(** the substitution must cover not only [aty_vars aty] but
    also every type variable and every region in [aty_spec] *)

val aty_filter : ?ghost:bool -> Spv.t -> aty -> aty
(** remove from the given arrow every effect that is covered
    neither by the arrow's arguments nor by the given pvset *)

val aty_app : aty -> pvsymbol -> spec * bool * vty
(** apply a function specification to a variable argument *)

val spec_check : ?full_xpost:bool -> spec -> vty -> unit
(** verify that the spec corresponds to the result type *)

val ity_of_vty : vty -> ity
val ty_of_vty  : vty -> ty
(** convert arrows to the unit type *)

val aty_vars : aty -> varset
val vty_vars : vty -> varset
(** collect the type variables and regions in arguments and values,
    but ignores the spec *)
