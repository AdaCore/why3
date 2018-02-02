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
open Ity
open Expr

(** {2 Type declarations} *)

type its_defn = private {
  itd_its          : itysymbol;
  itd_fields       : rsymbol list;
  itd_constructors : rsymbol list;
  itd_invariant    : term list;
  itd_witness      : expr list;
}

val create_plain_record_decl : priv:bool -> mut:bool ->
  preid -> tvsymbol list -> (bool * pvsymbol) list ->
  term list -> expr list -> its_defn
(** [create_plain_record_decl ~priv ~mut id args fields invl witn]
    creates a declaration for a non-recursive record type, possibly
    private and/or mutable. The known record fields are listed with
    their mutability status. The [priv] flag should be set to [true]
    for private records. The [mut] flag should be set to [true] to
    mark the new type as mutable even if it has no known mutable fields.
    This is the case for private mutable records with no known mutable
    fields, as well as for non-private records that have an invariant:
    marking such a type as mutable gives every value of this type a
    distinct identity, allowing us to track values with broken invariants.
    The [invl] parameter contains the list of invariant formulas that may
    only depend on free variables from [fields]. If the type is private,
    then every field occurring in [invl] must have an immutable type.
    The [witn] parameter provides a witness expression for each field
    of a plain record type (can be empty if there is no user witness).
    Abstract types are considered to be private records with no fields. *)

val create_rec_record_decl : itysymbol -> pvsymbol list -> its_defn
(** [create_rec_record_decl its fields] creates a declaration for
    a recursive record type. The type symbol should be created using
    [Ity.create_itysymbol_rec]. All fields must be immutable. *)

val create_plain_variant_decl :
  preid -> tvsymbol list -> (preid * (bool * pvsymbol) list) list -> its_defn
(** [create_plain_variant_decl id args constructors] creates a declaration
    for a non-recursive algebraic type. Each constructor field carries a
    Boolean flag denoting whether a projection function should be generated
    for this field. Any such field must be present in each constructor, so
    that the projection function is total. *)

val create_rec_variant_decl :
  itysymbol -> (preid * (bool * pvsymbol) list) list -> its_defn
(** [create_rec_variant_decl id args constructors] creates a declaration
    for a recursive algebraic type. The type symbol should be created using
    [Ity.create_itysymbol_rec]. Each constructor field carries a Boolean flag
    denoting whether a projection function should be generated for this field.
    Any such field must be present in each constructor, so that the projection
    function is total. All fields must be immutable. *)

val create_alias_decl : preid -> tvsymbol list -> ity -> its_defn
(** [create_alias_decl id args def] creates a new alias type declaration. *)

val create_range_decl : preid -> Number.int_range -> its_defn
(** [create_range_decl id ir] creates a new range type declaration. *)

val create_float_decl : preid -> Number.float_format -> its_defn
(** [create_float_decl id fp] creates a new float type declaration. *)

(** {2 Module declarations} *)

type pdecl = private {
  pd_node : pdecl_node;
  pd_pure : Decl.decl list;
  pd_meta : meta_decl list;
  pd_syms : Sid.t;
  pd_news : Sid.t;
  pd_tag  : int;
}

and pdecl_node = private
  | PDtype of its_defn list
  | PDlet  of let_defn
  | PDexn  of xsymbol
  | PDpure

and meta_decl = Theory.meta * Theory.meta_arg list

val axiom_of_invariant : its_defn -> term
(** [axiom_of_invariant itd] returns a closed formula that postulates
    the type invariant of [itd] for all values of the type *)

val create_type_decl : its_defn list -> pdecl list

val create_let_decl : let_defn -> pdecl

val create_exn_decl : xsymbol -> pdecl

val create_pure_decl : Decl.decl -> pdecl

(** {2 Built-in decls} *)

val pd_int : pdecl
val pd_real : pdecl
val pd_equ : pdecl
val pd_bool : pdecl
val pd_tuple : int -> pdecl
val pd_func : pdecl
val pd_func_app : pdecl

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> pdecl -> known_map
val merge_known : known_map -> known_map -> known_map

val find_its_defn : known_map -> itysymbol -> its_defn

(** {2 Pretty-printing} *)

val print_pdecl : Format.formatter -> pdecl -> unit
