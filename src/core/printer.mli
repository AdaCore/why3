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

(** {1 Task printing}

Utility functions for implementing printers for various provers

 *)

open Wstdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Task

exception BadSyntaxKind of char

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type prelude_export_map = prelude Mid.t
type interface = string list
type interface_map = interface Mid.t
type interface_export_map = interface Mid.t
type blacklist = string list

type field_info = {
  field_name: string; (** Printed field name *)
  field_trace: string; (** Model trace of the field, or [""] *)
  field_ident: ident option; (** Identifier of the field *)
}

(** The printing info is collected while printing a task to trace back elements
    in the output of the printer to elements in the task and the AST. *)
type printing_info = {
  why3_env : Env.env;
  (** The Why3 environment, retrieved from [printer_args], useful for builtin
      lsymbols *)
  vc_term_loc   : Loc.position option;
  (** The position of the term that triggers the VC *)
  vc_term_attrs : Sattr.t;
  (** The attributes of the term that triggers the VC *)
  queried_terms : (Term.lsymbol * Loc.position option * Sattr.t)  Mstr.t;
  (** The list of terms that were queried for the counter-example
     by the printer *)
  type_coercions : Sls.t Mty.t;
  (** For each type, the set of lsymbols defining a coercion to this type. *)
  type_fields : (lsymbol list) Mty.t;
  (** For each type, the list of lsymbols defining the fields for this record type
      and associated to meta_record_def. *)
  type_sorts : Ty.ty Mstr.t;
  (** Sorts defined in the prover output file. *)
  record_fields : (lsymbol list) Mls.t;
  (** Descriptions of the fields of all records. *)
  constructors: Term.lsymbol Mstr.t;
  (** Constructors. *)
  set_str: Sattr.t Mstr.t
  (** List of attributes corresponding to a printed constants (that was on the
     immediate term, not inside the ident) *)
}

val default_printing_info : Env.env -> printing_info
(** Empty mapping *)

type printer_args = {
  env           : Env.env;
  prelude       : prelude;
  th_prelude    : prelude_map;
  blacklist     : blacklist;
  printing_info : printing_info option ref;
  (* printing_info is a reference because it is easier to pass around in the
     printer *)
}

type printer = printer_args -> ?old:in_channel -> task Pp.pp
(** A printer receives a [printer_args] which is created from the information
   contained in the driver file. [old] is used for interactive prover where
   users edits the file. In this case the printer should try to keep the user
   edited part as much as possible *)

val register_printer : desc:Pp.formatted -> string -> printer -> unit
(** [register_printer ~desc name printer] Register the printer [printer] so that
    drivers of prover can mention it using [name]. *)

val lookup_printer : string -> printer

val list_printers : unit -> (string * Pp.formatted) list
(** List registered printers *)

(** {2 Use printers} *)

val print_prelude : prelude Pp.pp
(** Print a prelude *)

val print_th_prelude : task -> prelude_map Pp.pp
(** print the prelude of the theory present in the task *)

val print_interface : interface Pp.pp

val meta_syntax_type : meta
(** Meta used to mark in a task type that are associated with a syntax. Mainly
    used for the transformation which eliminate definitions of builtin type. *)

val meta_syntax_logic : meta
(** Meta used to mark in a task function that are associated with a syntax. *)

val meta_syntax_literal : meta
(** Meta used to mark in a task literals that will be printed particularly. *)

val meta_remove_prop : meta
(** Meta used to mark in a task proposition that must be removed before printing *)

val meta_remove_logic : meta
(** Meta used to mark in a task function that must be removed before printing *)

val meta_remove_type : meta
(** Meta used to mark in a task type that must be removed before printing *)

val meta_remove_def : meta
(** Meta used to mark in a task function that must be removed before printing *)

val meta_realized_theory : meta
(** Meta used for implementing modular realization of theories. The meta stores
    the association between a module and the name that should be used *)

val syntax_type : tysymbol -> string -> bool -> tdecl
(** create a meta declaration for the builtin syntax of a type *)

val syntax_logic : lsymbol -> string -> bool -> tdecl
(** create a meta declaration for the builtin syntax of a function *)

val syntax_literal : tysymbol -> string -> bool -> tdecl
(** create a meta declaration for the builtin syntax of a literal *)

val remove_prop : prsymbol -> tdecl
(** create a meta declaration for a proposition to remove *)

val check_syntax_type: tysymbol -> string -> unit
(** [check_syntax_type tys syntax] check that [syntax] doesn't mention arguments
    that [tys] doesn't have *)

val check_syntax_logic: lsymbol -> string -> unit
(** [check_syntax_logic ls syntax] check that [syntax] doesn't mention arguments
   that [ls] doesn't have *)

type syntax_map = (string*int) Mid.t
(* [syntax_map] maps the idents of removed props to "" *)

val get_syntax_map : task -> syntax_map
val add_syntax_map : tdecl -> syntax_map -> syntax_map
(* interprets a declaration as a syntax rule, if any *)

val get_rliteral_map : task -> syntax_map
val add_rliteral_map : tdecl -> syntax_map -> syntax_map

val query_syntax : syntax_map -> ident -> string option

val syntax_arity : string -> int
(** [syntax_arity s] returns the largest [i] such that the parameter
    [%i] occurs in [s]. Formatting an argument list for [s] will only
    succeed if the argument list has size [syntax_arity s] or more. *)

val syntax_arguments_prec : string -> (int -> 'a Pp.pp) -> int list -> 'a list Pp.pp
(** [syntax_arguments_prec templ print_arg prec_list fmt l] prints in the
    formatter [fmt] the list [l] using the template [templ], the printer
    [print_arg], and the precedence list [prec_list] *)

val syntax_arguments : string -> 'a Pp.pp -> 'a list Pp.pp
(** [syntax_arguments templ print_arg fmt l] prints in the
    formatter [fmt] the list [l] using the syntax [templ], and the printer
    [print_arg] *)

val gen_syntax_arguments_prec :
  Format.formatter -> string ->
  (Format.formatter -> int -> char option -> int -> unit) -> int list -> unit

val syntax_arguments_typed_prec :
  string -> (int -> term Pp.pp) -> ty Pp.pp -> term -> int list -> term list Pp.pp
(** [syntax_arguments_typed_prec templ print_arg print_type t prec_list fmt l]
    prints in the formatter [fmt] the list [l] using the template [templ], the
    printers [print_arg] and [print_type], and the precedence list [prec_list].
    The term [t] should be akin to [Tapp (_, l)] and is used to fill ["%t0"]
    and ["%si"]. *)

val syntax_arguments_typed :
  string -> term Pp.pp -> ty Pp.pp -> term -> term list Pp.pp
(** [syntax_arguments_typed templ print_arg print_type t fmt l]
    prints in the formatter [fmt] the list [l] using the template [templ], the
    printers [print_arg] and [print_type].
    The term [t] should be akin to [Tapp (_, l)] and is used to fill ["%t0"]
    and ["%si"]. *)

val syntax_range_literal :
  ?cb:(Number.int_constant Pp.pp option) -> string -> Number.int_constant Pp.pp

val syntax_float_literal :
  string -> Number.float_format -> Number.real_constant Pp.pp

(** {2 pretty-printing transformations (useful for caching)} *)

val on_syntax_map : (syntax_map -> 'a Trans.trans) -> 'a Trans.trans

val sprint_tdecl :
  ('a -> Format.formatter -> Theory.tdecl -> 'a * string list) ->
    Theory.tdecl -> 'a * string list -> 'a * string list

val sprint_decl :
  ('a -> Format.formatter -> Decl.decl -> 'a * string list) ->
    Theory.tdecl -> 'a * string list -> 'a * string list

(** {2 Exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedTerm of term * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string

val unsupportedType : ty   -> string -> 'a
(** Should be used by the printer for handling the error of an unsupported type *)

val unsupportedTerm : term -> string -> 'a
(** Should be used by the printer for handling the error of an unsupported term *)

val unsupportedPattern : pattern -> string -> 'a
(** Should be used by the printer for handling the error of an unsupported pattern *)

val unsupportedDecl : decl -> string -> 'a
(** Should be used by the printer for handling the error of an unsupported declaration *)

val notImplemented  :         string -> 'a
(** Should be used by the printer for handling partial implementation *)

(** {3 Functions that catch inner error} *)

exception Unsupported of string
(** This exception must be raised only inside a call
    of one of the catch_* functions below *)

val unsupported : string -> 'a

val catch_unsupportedType : (ty -> 'a) -> (ty -> 'a)
(** [catch_unsupportedType f] return a function which applied on [arg]:
    - return [f arg] if [f arg] does not raise {!Unsupported} exception
    - raise [UnsupportedType (arg,s)] if [f arg] raises [Unsupported s]*)

val catch_unsupportedTerm : (term -> 'a) -> (term -> 'a)
(** same as {!catch_unsupportedType} but use {!UnsupportedTerm}
    instead of {!UnsupportedType} *)

val catch_unsupportedDecl : (decl -> 'a) -> (decl -> 'a)
(** same as {!catch_unsupportedType} but use {!UnsupportedDecl}
    instead of {!UnsupportedType} *)
