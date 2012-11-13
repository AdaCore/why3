(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
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

(** individual types (first-order types w/o effects) *)

module rec T : sig

  type varset = private {
    vars_tv  : Stv.t;
    vars_reg : Mreg.Set.t;
  }
  (* the set of variables, e.g. of an individual type. An individual program
     type can contain type and region variables *)

  type varmap = varset Mid.t

  type itysymbol = private {     (* the type of a type symbol *)
    its_pure : tysymbol;         (* the corresponding pure type *)
    its_args : tvsymbol list;    (* the set of bound variables *)
    its_regs : region list;      (* the set of regions *)
    its_def  : ity option;       (* the definition of the type symbol *)
    its_inv  : bool;             (* does the type have an invariant? *)
    its_abst : bool;             (* is the type abstract = does it have a model
                                    view? *)
    its_priv : bool;             (* is the type private? *)
  }

  and ity = private {            (* the actual type structure *)
    ity_node : ity_node;         (* the kind of the type *)
    ity_vars : varset;           (* the variables bound by the type *)
    ity_tag  : Weakhtbl.tag;
  }

  and ity_node = private
    | Ityvar of tvsymbol                           (* simply a type variable *)
    | Itypur of tysymbol * ity list                (* a pure type *)
    | Ityapp of itysymbol * ity list * region list
                           (* a regular type application, with type and region
                              arguments *)

  and region = private {
    reg_name  : ident;               (* the name of the region *)
    reg_ity   : ity;                 (* the type of the region *)
  }

end
and Mreg : sig include Map.S with type key = T.region end

open T

module Mits : Map.S with type key = itysymbol
module Sits : Mits.Set
module Hits : XHashtbl.S with type key = itysymbol
module Wits : Weakhtbl.S with type key = itysymbol

module Mity : Map.S with type key = ity
module Sity : Mity.Set
module Hity : XHashtbl.S with type key = ity
module Wity : Weakhtbl.S with type key = ity

module Sreg : Mreg.Set
module Hreg : XHashtbl.S with type key = region
module Wreg : Weakhtbl.S with type key = region

val its_equal : itysymbol -> itysymbol -> bool
val ity_equal : ity -> ity -> bool

val its_hash : itysymbol -> int
val ity_hash : ity -> int

val reg_equal : region -> region -> bool
val reg_hash : region -> int

exception BadItyArity of itysymbol * int * int
exception BadRegArity of itysymbol * int * int
exception DuplicateRegion of region
exception UnboundRegion of region

val create_region : preid -> ity -> region

val create_itysymbol :
  preid -> ?abst:bool -> ?priv:bool -> ?inv:bool ->
    tvsymbol list -> region list -> ity option -> itysymbol

val ity_var : tvsymbol -> ity
val ity_pur : tysymbol -> ity list -> ity

val ity_app : itysymbol -> ity list -> region list -> ity
val ity_app_fresh : itysymbol -> ity list -> ity

(* all aliases expanded, all regions removed *)
val ty_of_ity : ity -> ty

(* replaces every [Tyapp] with [Itypur] *)
val ity_of_ty : ty -> ity

(* generic traversal functions *)

val ity_map : (ity -> ity) -> ity -> ity
val ity_fold : ('a -> ity -> 'a) -> 'a -> ity -> 'a
val ity_all : (ity -> bool) -> ity -> bool
val ity_any : (ity -> bool) -> ity -> bool

(* traversal functions on type symbols *)

val ity_s_fold :
  ('a -> itysymbol -> 'a) -> ('a -> tysymbol -> 'a) -> 'a -> ity -> 'a

val ity_s_all : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool
val ity_s_any : (itysymbol -> bool) -> (tysymbol -> bool) -> ity -> bool

val its_clone : Theory.symbol_map -> itysymbol Mits.t * region Mreg.t

(* traversal functions on type variables and regions *)

val ity_v_map : (tvsymbol -> ity) -> (region -> region) -> ity -> ity

val ity_closed : ity -> bool
val ity_pure : ity -> bool
val ity_inv : ity -> bool

(* these functions attend the sub-regions *)

val reg_fold : (region -> 'a -> 'a) -> varset -> 'a -> 'a
val reg_any  : (region -> bool) -> varset -> bool
val reg_all  : (region -> bool) -> varset -> bool
val reg_iter : (region -> unit) -> varset -> unit

val reg_occurs : region -> varset -> bool

(* built-in types *)

val ts_unit : tysymbol (* the same as [Ty.ts_tuple 0] *)
val ty_unit : ty

val ity_int : ity
val ity_bool : ity
val ity_unit : ity

exception RegionMismatch of region * region
exception TypeMismatch of ity * ity

type ity_subst = private {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t;
}

val ity_subst_empty : ity_subst

val ity_match : ity_subst -> ity -> ity -> ity_subst

val reg_match : ity_subst -> region -> region -> ity_subst

val ity_equal_check : ity -> ity -> unit

val ity_full_inst : ity_subst -> ity -> ity

val reg_full_inst : ity_subst -> region -> region

val vars_empty : varset

val vars_union : varset -> varset -> varset

val vars_merge : varmap -> varset -> varset

val vars_freeze : varset -> ity_subst

val create_varset : Stv.t -> Sreg.t -> varset

(* exception symbols *)
type xsymbol = private {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

val xs_equal : xsymbol -> xsymbol -> bool

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

val create_xsymbol : preid -> ity -> xsymbol

module Mexn: Map.S with type key = xsymbol
module Sexn: Mexn.Set

(** effects *)

type effect = private {
  eff_reads  : Sreg.t;
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostr : Sreg.t; (* ghost reads *)
  eff_ghostw : Sreg.t; (* ghost writes *)
  eff_ghostx : Sexn.t; (* ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
}

val eff_empty : effect
val eff_union : effect -> effect -> effect
val eff_ghostify : effect -> effect

val eff_read  : effect -> ?ghost:bool -> region -> effect
val eff_write : effect -> ?ghost:bool -> region -> effect
val eff_raise : effect -> ?ghost:bool -> xsymbol -> effect
val eff_reset : effect -> region -> effect

val eff_refresh : effect -> region -> region -> effect
val eff_assign : effect -> ?ghost:bool -> region -> ity -> effect

val eff_remove_raise : effect -> xsymbol -> effect

val eff_stale_region : effect -> varset -> bool

exception IllegalAlias of region

val eff_full_inst : ity_subst -> effect -> effect

val eff_filter : varset -> effect -> effect

val eff_is_empty : effect -> bool

(** specification *)

type pre = term          (* precondition: pre_fmla *)
type post = term         (* postcondition: eps result . post_fmla *)
type xpost = post Mexn.t (* exceptional postconditions *)

type variant = term * lsymbol option (* tau * (tau -> tau -> prop) *)

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

(** program variables *)

type vty_value = private {         (* the type of a program variable *)
  vtv_ity   : ity;                 (* the underlying program type *)
  vtv_ghost : bool;                (* am I a ghost variable? *)
  vtv_mut   : region option;       (* if this field is not None *)
}

val vty_value : ?ghost:bool -> ?mut:region -> ity -> vty_value

val vtv_unmut : vty_value -> vty_value (* remove mutability *)

type pvsymbol = private { (* a program variable *)
  pv_vs   : vsymbol;      (* the variable symbol *)
  pv_vtv  : vty_value;    (* the program type *)
  pv_vars : varset;
       (* the type and region variables of the variable type. This is equal to
          pv_vtv.vtv_ity.ity_vars plus the region in pv_vtv.vtv_mut. *)
}

module Mpv : Map.S with type key = pvsymbol
module Spv : Mpv.Set
module Hpv : XHashtbl.S with type key = pvsymbol
module Wpv : Weakhtbl.S with type key = pvsymbol

val pv_equal : pvsymbol -> pvsymbol -> bool

val create_pvsymbol : preid -> vty_value -> pvsymbol
(* from an id and a type, create a pvsymbol. Note that this also creates the
   underlying vsymbol (see pvsymbol.pv_vs field), and an entry
   vsymbol -> pvsymbol is created in a private map. *)

val restore_pv : vsymbol -> pvsymbol
  (* return the program variable [pvs] such that pvs.pv_vs is equal to the
     argument. raises Not_found if the argument is not a pv_vs *)

val restore_pv_by_id : ident -> pvsymbol
  (* raises Not_found if the argument is not a pv_vs.vs_name *)

(** program types *)

type vty =
  | VTvalue of vty_value      (* either an individual type *)
  | VTarrow of vty_arrow      (* or an arrow type with a spec *)

and vty_arrow = private {
  vta_args   : pvsymbol list;
  vta_result : vty;
  vta_spec   : spec;
  vta_ghost  : bool;
}

exception UnboundException of xsymbol

(* every raised exception must have a postcondition in spec.c_xpost *)
val vty_arrow : pvsymbol list -> ?spec:spec -> ?ghost:bool -> vty -> vty_arrow

(* this only compares the types of arguments and results, and ignores
   the spec. In other words, only the type variables and regions in
   [vta_vars vta] are matched. The caller should supply a "freezing"
   substitution that covers all external type variables and regions. *)
val vta_vars_match : ity_subst -> vty_arrow -> vty_arrow -> ity_subst

(* the substitution must cover not only [vta_vars vta] but
   also every type variable and every region in vta_spec *)
val vta_full_inst : ity_subst -> vty_arrow -> vty_arrow

(* remove from the given arrow every effect that is covered
   neither by the arrow's arguments nor by the given varmap *)
val vta_filter : varmap -> vty_arrow -> vty_arrow

(* apply a function specification to a variable argument *)
val vta_app : vty_arrow -> pvsymbol -> spec * vty

(* test for ghostness and convert to ghost *)
val vty_ghost : vty -> bool
val vty_ghostify : vty -> vty

(* verify that the spec corresponds to the result type *)
val spec_check : spec -> vty -> unit

(* convert arrows to the unit type *)
val ity_of_vty : vty -> ity
val ty_of_vty  : vty -> ty

(* collects the type variables and regions in arguments and values,
   but ignores the spec *)
val vta_vars : vty_arrow -> varset
val vty_vars : vty -> varset
