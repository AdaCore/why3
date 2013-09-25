(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
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

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type blacklist = string list

type 'a pp = Format.formatter -> 'a -> unit

type printer_args =
  { env : Env.env;
    prelude : prelude;
    prelude_map : prelude_map;
    blacklist : blacklist
  }
type printer =
  printer_args -> ?old:in_channel -> task pp

val register_printer : desc:Pp.formatted -> string -> printer -> unit

val lookup_printer : string -> printer

val list_printers : unit -> (string * Pp.formatted) list

(** {2 use printers} *)

val print_prelude : prelude pp
val print_th_prelude : task -> prelude_map pp

val meta_syntax_type : meta
val meta_syntax_logic : meta
val meta_remove_prop : meta
val meta_remove_logic : meta
val meta_remove_type : meta
val meta_realized_theory : meta

val syntax_type : tysymbol -> string -> tdecl
val syntax_logic : lsymbol -> string -> tdecl
val remove_prop : prsymbol -> tdecl

val check_syntax_type: tysymbol -> string -> unit
val check_syntax_logic: lsymbol -> string -> unit

type syntax_map = string Mid.t
(* [syntax_map] maps the idents of removed props to "" *)

val get_syntax_map : task -> syntax_map
val add_syntax_map : tdecl -> syntax_map -> syntax_map
  (* interprets a declaration as a syntax rule, if any *)

val query_syntax : syntax_map -> ident -> string option

val syntax_arguments : string -> 'a pp -> 'a list pp
(** (syntax_arguments templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

val syntax_arguments_typed :
  string -> term pp -> ty pp -> term -> term list pp
(** (syntax_arguments templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

(** {2 pretty-printing transformations (useful for caching)} *)

val fold_tdecls : (syntax_map -> tdecl -> 'a -> 'a) -> 'a -> 'a Trans.trans

val sprint_tdecls : (syntax_map -> tdecl pp) -> string list Trans.trans
val sprint_decls  : (syntax_map -> decl  pp) -> string list Trans.trans

(** {2 exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedTerm of term * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string

val unsupportedType : ty   -> string -> 'a
val unsupportedTerm : term -> string -> 'a
val unsupportedDecl : decl -> string -> 'a
val notImplemented  :         string -> 'a

(** {3 functions that catch inner error} *)

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

