(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Helpers for constructing program with the parse tree API} *)

open Loc
open Ptree

(** {2 identifiers} *)

val ident : ?attrs:attr list -> ?loc:position -> string -> ident
(** [ident ?attr ?loc s] produce the identifier named [s]
   optionally with the given attributes and source location *)

val qualid : string list -> qualid
(** [qualid l] produces the qualified identifier given by the path
   [l], a list in the style of [["int";"Int"]] *)

val const : ?kind:Number.int_literal_kind -> int -> Constant.constant

val unit_binder : ?loc:position -> unit -> binder list

val one_binder : ?loc:position -> ?ghost:bool -> ?pty:pty -> string  -> binder list

(** {2 terms and formulas} *)

val term : ?loc:position -> term_desc -> term

val tconst : ?loc:position -> int -> term

val tvar : ?loc:position -> qualid -> term

val tapp : ?loc:position -> qualid -> term list -> term

val pat : ?loc:position -> pat_desc -> pattern

val pat_var : ?loc:position -> ident -> pattern

(** {2 program expressions} *)

val break_id : string
val continue_id :string
val return_id : string

val expr : ?loc:position -> expr_desc -> expr

val econst : ?loc:position -> int -> expr

val eapp : ?loc:position -> qualid -> expr list -> expr

val eapply : ?loc:position -> expr -> expr -> expr

val evar : ?loc:position -> qualid -> expr

val empty_spec : spec

(** {2 declarations} *)

val use : ?loc:Loc.position -> import:bool -> string list -> decl
(** [use l] produces the equivalent of ["use (import) path"] where [path] is denoted by [l] *)

val global_var_decl : pty -> string -> ident * decl
(** [global_var_decl ty id] declares a global mutable variable `id` of
    type `ty`. It returns both the variable identifier and the
    declaration itself *)

(** {2 Declarations in top-down style}

The following helpers allows one to create modules, declarations
   inside modules, and program functions in a top-down style, instead
   of the bottom-up style above

This extra layer commes into two flavors, a functional one, or say a
   monadic style, with an explicit state of declarations under
   constructions ; and an imperative style.  *)

(** Extra helpers for creating declarations in top-down style,
    functional interface *)
module F : sig

  type state

  val create : unit -> state

  val begin_module : state -> ?loc:position -> string -> state

  val use : state -> ?loc:Loc.position -> import:bool -> string list -> state
  (** see [use_import] above *)

  val add_prop : state -> Decl.prop_kind -> ?loc:Loc.position -> string -> term -> state

  val add_global_var_decl : state -> pty -> string -> ident * state

  val begin_let : state -> ?ghost:bool -> ?diverges:bool -> ?ret_type:pty -> string -> binder list -> state

  val add_pre : state -> term -> state

  val add_writes : state -> term list -> state

  val add_post : state -> term -> state

  val add_body : state -> expr -> state

  val end_module : state -> state

  val get_mlw_file : state -> mlw_file

end

(** Extra helpers for creating declarations in top-down style,
    imperative interface. Beware that these functions are not
    thread-safe *)
module I : sig

  val begin_module : ?loc:position -> string -> unit
  (** see [begin_module] above *)

  val use : ?loc:Loc.position -> import:bool -> string list -> unit
  (** see [use_import] above *)

  val add_prop : Decl.prop_kind -> ?loc:Loc.position -> string -> term -> unit

  val add_global_var_decl : pty -> string -> ident

  val begin_let : ?ghost:bool -> ?diverges:bool -> ?ret_type:pty -> string -> binder list -> unit

  val add_pre : term -> unit

  val add_writes : term list -> unit

  val add_post : term -> unit

  val add_body : expr -> unit

  val end_module : unit -> unit

  val get_mlw_file : unit -> mlw_file


end
