(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Comment *)

val print_comments : Format.formatter -> string -> ?end_tok:string -> term -> unit
(** Prints the comments of a term (if present) line by line and aligned.
    [print_comment fmt "/*" ~end_tok:"*/" t] prints the labels starting
    with "comment:" of term t to formatter fmt,
    each line of the comment being surrounded by "/*" "*/". *)

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type blacklist = string list

type 'a pp = Format.formatter -> 'a -> unit

(* Makes it possible to estabilish traceability from names
in the output of the printer to elements of AST in its input. *)
type printer_mapping = {
  lsymbol_m     : string -> Term.lsymbol;
  vc_term_loc   : Loc.position option;
  (* The position of the term that triggers the VC *)
  queried_terms : Term.term Stdlib.Mstr.t;
  (* The list of terms that were queried for the counter-example
     by the printer *)
}

type printer_args = {
  env        : Env.env;
  prelude    : prelude;
  th_prelude : prelude_map;
  blacklist  : blacklist;
  mutable printer_mapping : printer_mapping;
}

type printer = printer_args -> ?old:in_channel -> task pp

val get_default_printer_mapping : printer_mapping

val register_printer : desc:Pp.formatted -> string -> printer -> unit

val lookup_printer : string -> printer

val list_printers : unit -> (string * Pp.formatted) list

(** {2 Use printers} *)

val print_prelude : prelude pp
val print_th_prelude : task -> prelude_map pp

val meta_syntax_type : meta
val meta_syntax_logic : meta
val meta_syntax_converter : meta
val meta_syntax_literal : meta
val meta_remove_prop : meta
val meta_remove_logic : meta
val meta_remove_type : meta
val meta_realized_theory : meta

val syntax_type : tysymbol -> string -> bool -> tdecl
val syntax_logic : lsymbol -> string -> bool -> tdecl
val syntax_converter : lsymbol -> string -> bool -> tdecl
val syntax_literal : tysymbol -> string -> bool -> tdecl
val remove_prop : prsymbol -> tdecl

val check_syntax_type: tysymbol -> string -> unit
val check_syntax_logic: lsymbol -> string -> unit

type syntax_map = (string*int) Mid.t
(* [syntax_map] maps the idents of removed props to "" *)
type converter_map = (string*int) Mls.t

val get_syntax_map : task -> syntax_map
val add_syntax_map : tdecl -> syntax_map -> syntax_map
(* interprets a declaration as a syntax rule, if any *)

val get_converter_map : task -> converter_map

val get_rliteral_map : task -> syntax_map
val add_rliteral_map : tdecl -> syntax_map -> syntax_map

val query_syntax : syntax_map -> ident -> string option
val query_converter : converter_map -> lsymbol -> string option

val syntax_arguments : string -> 'a pp -> 'a list pp
(** (syntax_arguments templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

val gen_syntax_arguments_typed :
  ('a -> 'b) -> ('a -> 'b array) -> string -> 'a pp -> 'b pp -> 'a -> 'a list pp

val syntax_arguments_typed :
  string -> term pp -> ty pp -> term -> term list pp
(** (syntax_arguments templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

val syntax_range_literal :
  string -> Number.integer_constant pp

val syntax_float_literal :
  string -> Number.float_format -> Number.real_constant pp

(** {2 pretty-printing transformations (useful for caching)} *)

val on_syntax_map : (syntax_map -> 'a Trans.trans) -> 'a Trans.trans

val on_converter_map : (converter_map -> 'a Trans.trans) -> 'a Trans.trans

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
val unsupportedTerm : term -> string -> 'a
val unsupportedPattern : pattern -> string -> 'a
val unsupportedDecl : decl -> string -> 'a
val notImplemented  :         string -> 'a

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
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedDecl : (decl -> 'a) -> (decl -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedDecl]
    instead of [UnsupportedType] *)
