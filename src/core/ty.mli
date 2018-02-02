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

(** Types *)

open Ident

(** {2 Type variables} *)

type tvsymbol = private {
  tv_name : ident;
}

module Mtv : Extmap.S with type key = tvsymbol
module Stv : Extset.S with module M = Mtv
module Htv : Exthtbl.S with type key = tvsymbol

val tv_compare : tvsymbol -> tvsymbol -> int
val tv_equal : tvsymbol -> tvsymbol -> bool
val tv_hash : tvsymbol -> int

val create_tvsymbol : preid -> tvsymbol

val tv_of_string : string -> tvsymbol

(** {2 Type symbols and types} *)

type 'a type_def =
  | NoDef
  | Alias of 'a
  | Range of Number.int_range
  | Float of Number.float_format

type tysymbol = private {
  ts_name      : ident;
  ts_args      : tvsymbol list;
  ts_def       : ty type_def;
}

and ty = private {
  ty_node : ty_node;
  ty_tag  : Weakhtbl.tag;
}

and ty_node = private
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

module Mts : Extmap.S with type key = tysymbol
module Sts : Extset.S with module M = Mts
module Hts : Exthtbl.S with type key = tysymbol
module Wts : Weakhtbl.S with type key = tysymbol

module Mty : Extmap.S with type key = ty
module Sty : Extset.S with module M = Mty
module Hty : Exthtbl.S with type key = ty
module Wty : Weakhtbl.S with type key = ty

val ts_compare : tysymbol -> tysymbol -> int
val ty_compare : ty -> ty -> int

val ts_equal : tysymbol -> tysymbol -> bool
val ty_equal : ty -> ty -> bool

val ts_hash : tysymbol -> int
val ty_hash : ty -> int

exception BadTypeArity of tysymbol * int
exception DuplicateTypeVar of tvsymbol
exception UnboundTypeVar of tvsymbol
exception IllegalTypeParameters
exception BadFloatSpec
exception EmptyRange

val create_tysymbol : preid -> tvsymbol list -> ty type_def -> tysymbol

val ty_var : tvsymbol -> ty
val ty_app : tysymbol -> ty list -> ty

(** {2 Type definition utilities} *)

val type_def_map : ('a -> 'a) -> 'a type_def -> 'a type_def
val type_def_fold : ('a -> 'b -> 'a) -> 'a -> 'b type_def -> 'a

val is_alias_type_def : 'a type_def -> bool
val is_range_type_def : 'a type_def -> bool
val is_float_type_def : 'a type_def -> bool

(** {2 Generic traversal functions} *)

(** traverse only one level of constructor, if you want full traversal
    you need to call those function inside your function *)
val ty_map : (ty -> ty) -> ty -> ty
val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_all : (ty -> bool) -> ty -> bool
val ty_any : (ty -> bool) -> ty -> bool

(** {2 Variable-wise map/fold} *)

(** visits every variable of the type *)
val ty_v_map : (tvsymbol -> ty) -> ty -> ty
val ty_v_fold : ('a -> tvsymbol -> 'a) -> 'a -> ty -> 'a
val ty_v_all : (tvsymbol -> bool) -> ty -> bool
val ty_v_any : (tvsymbol -> bool) -> ty -> bool

(** {2 Symbol-wise map/fold} *)

(** visits every symbol of the type *)
val ty_s_map : (tysymbol -> tysymbol) -> ty -> ty
val ty_s_fold : ('a -> tysymbol -> 'a) -> 'a -> ty -> 'a
val ty_s_all : (tysymbol -> bool) -> ty -> bool
val ty_s_any : (tysymbol -> bool) -> ty -> bool

exception TypeMismatch of ty * ty

val ty_match : ty Mtv.t -> ty -> ty -> ty Mtv.t
(** [ty_match sigma0 pat sub] returns a type substitution [sigma] such
    that [sigma pat = sub]. Raises TypeMismatch if no substitution
    exists.
*)

val ts_match_args : tysymbol -> ty list -> ty Mtv.t
val ty_match_args : ty -> ty Mtv.t

val ty_inst  : ty Mtv.t -> ty -> ty
val ty_freevars : Stv.t -> ty -> Stv.t
val ty_closed : ty -> bool
(** [ty_closed ty] returns true when [ty] is not polymorphic *)

val ty_equal_check : ty -> ty -> unit

(* built-in symbols *)

val ts_int  : tysymbol
val ts_real : tysymbol
val ts_bool : tysymbol

val ty_int  : ty
val ty_real : ty
val ty_bool : ty

val ts_func : tysymbol

val ty_func : ty -> ty -> ty
val ty_pred : ty -> ty (* ty_pred 'a == ty_func 'a bool *)

val ts_tuple : int -> tysymbol
val ty_tuple : ty list -> ty

val is_ts_tuple : tysymbol -> bool
val is_ts_tuple_id : ident -> int option

(** {2 Operations on [ty option]} *)

exception UnexpectedProp

val oty_compare : ty option -> ty option -> int
val oty_equal : ty option -> ty option -> bool
val oty_hash  : ty option -> int

val oty_type : ty option -> ty
val oty_cons : ty list -> ty option -> ty list

val oty_match : ty Mtv.t -> ty option -> ty option -> ty Mtv.t
val oty_inst  : ty Mtv.t -> ty option -> ty option
val oty_freevars : Stv.t -> ty option -> Stv.t
