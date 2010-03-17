(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Ident
open Ty
open Term

(** Declarations *)

(* type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(* logic declaration *)

type ls_defn

type logic_decl = lsymbol * ls_defn option

val make_ls_defn : lsymbol -> vsymbol list -> expr -> logic_decl
val make_fs_defn : lsymbol -> vsymbol list -> term -> logic_decl
val make_ps_defn : lsymbol -> vsymbol list -> fmla -> logic_decl

val open_ls_defn : ls_defn -> vsymbol list * expr
val open_fs_defn : ls_defn -> vsymbol list * term
val open_ps_defn : ls_defn -> vsymbol list * fmla

val ls_defn_axiom : ls_defn -> fmla

(* inductive predicate declaration *)

type prop

module Spr : Set.S with type elt = prop
module Mpr : Map.S with type key = prop
module Hpr : Hashtbl.S with type key = prop

val create_prop : preid -> prop
val pr_name     : prop -> ident

type prop_fmla = prop * fmla

type ind_decl  = lsymbol * prop_fmla list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * prop * fmla

(** Context and Theory *)

module Snm : Set.S with type elt = string
module Mnm : Map.S with type key = string

type theory = private {
  th_name   : ident;        (* theory name *)
  th_ctxt   : context;      (* theory declarations *)
  th_export : namespace;    (* exported namespace *)
  th_local  : Sid.t;        (* locally declared idents *)
}

and namespace = private {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_pr : prop_fmla Mnm.t;  (* propositions *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

and context = private {
  ctxt_env    : env;
  ctxt_decl   : decl;
  ctxt_prev   : context option;
  ctxt_known  : decl Mid.t;
  ctxt_cloned : Sid.t Mid.t;
  ctxt_tag    : int;
}

and env

and decl = private {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)
  | Duse   of theory                         (* depend on a theory *)
  | Dclone of theory * (ident * ident) list  (* replicate a theory *)

(** Declaration constructors *)

val create_ty_decl : ty_decl list -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_decl list -> decl
val create_prop_decl : prop_kind -> prop -> fmla -> decl

(* separate independent groups of declarations *)

val create_ty_decls : ty_decl list -> decl list
val create_logic_decls : logic_decl list -> decl list
val create_ind_decls : ind_decl list -> decl list

(* exceptions *)

exception ConstructorExpected of lsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of tvsymbol

exception InvalidIndDecl of lsymbol * prop
exception TooSpecificIndDecl of lsymbol * prop * term
exception NonPositiveIndDecl of lsymbol * prop * lsymbol

exception IllegalConstructor of lsymbol
exception BadLogicDecl of ident
exception UnboundVars of Svs.t
exception ClashIdent of ident
exception EmptyDecl

(** Environements *)

type retrieve_theory = env -> string list -> theory Mnm.t
  (* a function of type retrieve_theory is a partial function it can
     raise Not_found if it can't retrieve this theory*)

val create_env : retrieve_theory -> env


exception TheoryNotFound of string list * string

val find_theory : env -> string list -> string -> theory

val env_tag : env -> int

(** Context constructors and utilities *)

type th_inst = {
  inst_ts    : tysymbol Mts.t;
  inst_ls    : lsymbol  Mls.t;
  inst_lemma : Spr.t;
  inst_goal  : Spr.t;
}

val empty_inst : th_inst

module Context : sig

  val init_context : env -> context

  val add_decl : context -> decl -> context

  val use_export   : context -> theory -> context
  val clone_export : context -> theory -> th_inst -> context

  (* bottom-up, tail-recursive traversal functions *)
  val ctxt_fold : ('a -> decl -> 'a) -> 'a -> context -> 'a
  val ctxt_iter : (decl -> unit) -> context -> unit

  (* top-down list of declarations *)
  val get_decls : context -> decl list

  exception UnknownIdent of ident
  exception RedeclaredIdent of ident

  exception NonLocal of ident
  exception CannotInstantiate of ident
  exception BadInstance of ident * ident

end

(** Namespace search tools *)

val ns_find_ts   : namespace -> string list -> tysymbol
val ns_find_ls   : namespace -> string list -> lsymbol
val ns_find_pr   : namespace -> string list -> prop_fmla

val ns_find_prop : namespace -> string list -> prop
val ns_find_fmla : namespace -> string list -> fmla

(** Theory constructors and utilities *)

type theory_uc  (* a theory under construction *)

module TheoryUC : sig

  val create_theory : env -> preid -> theory_uc
  val close_theory  : theory_uc -> theory

  val add_decl : theory_uc -> decl -> theory_uc

  val open_namespace  : theory_uc -> theory_uc
  val close_namespace : theory_uc -> bool -> string option -> theory_uc

  val use_export   : theory_uc -> theory -> theory_uc
  val clone_export : theory_uc -> theory -> th_inst -> theory_uc

  val get_namespace : theory_uc -> namespace

  exception CloseTheory
  exception NoOpenedNamespace
  exception ClashSymbol of string

end

val builtin_name : string

(*
(** Debugging *)

val print_ident : Format.formatter -> ident -> unit
val print_uc : Format.formatter -> theory_uc -> unit
val print_ctxt : Format.formatter -> context -> unit
val print_th : Format.formatter -> theory -> unit

(* Utils *)

exception NotGoalContext
val goal_of_ctxt : context -> prop
(* goal_of_ctxt ctxt return the goal of a goal context
   the ctxt must end with a goal.*)
*)
