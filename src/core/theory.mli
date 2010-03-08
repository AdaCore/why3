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

(** Named propositions *)

type prop = private {
  pr_name : ident;
  pr_fmla : fmla;
}

module Spr : Set.S with type elt = prop
module Mpr : Map.S with type key = prop
module Hpr : Hashtbl.S with type key = prop

val create_prop : preid -> fmla -> prop

(** Declarations *)

(* type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(* logic declaration *)

type fs_defn
type ps_defn

type logic_decl =
  | Lfunction  of lsymbol * fs_defn option
  | Lpredicate of lsymbol * ps_defn option

val make_fs_defn : lsymbol -> vsymbol list -> term -> fs_defn
val make_ps_defn : lsymbol -> vsymbol list -> fmla -> ps_defn

val open_fs_defn : fs_defn -> lsymbol * vsymbol list * term
val open_ps_defn : ps_defn -> lsymbol * vsymbol list * fmla

val fs_defn_axiom : fs_defn -> fmla
val ps_defn_axiom : ps_defn -> fmla

(* inductive predicate declaration *)

type ind_decl = lsymbol * prop list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * prop

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
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
  ns_pr : prop Mnm.t;       (* propositions *)
}

and context = private {
  ctxt_decls : (decl * context) option;
  ctxt_known : decl Mid.t;
  ctxt_cloned : ident list Mid.t;
  ctxt_tag   : int;
}

and decl = private {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)
  | Duse   of theory                (* depend on a theory *)
  | Dclone of (ident * ident) list  (* replicate a theory *)

(** Declaration constructors *)

val create_ty_decl : ty_decl list -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_decl list -> decl
val create_prop_decl : prop_kind -> prop -> decl
val create_prop_and_decl : prop_kind -> preid -> fmla -> decl

(* exceptions *)

exception ConstructorExpected of lsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of ident

exception IllegalConstructor of lsymbol
exception UnboundVars of Svs.t
exception BadDecl of ident

(** Context constructors and utilities *)

type th_inst = {
  inst_ts    : tysymbol Mts.t;
  inst_ls    : lsymbol  Mls.t;
  inst_lemma : Spr.t;
  inst_goal  : Spr.t;
}

val empty_inst : th_inst

module Context : sig

  val empty_context : context

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

(** Theory constructors and utilities *)

type theory_uc  (* a theory under construction *)

module Theory : sig

  val create_theory : preid -> theory_uc
  val close_theory  : theory_uc -> theory

  val add_decl : theory_uc -> decl -> theory_uc

  val open_namespace  : theory_uc -> theory_uc
  val close_namespace : theory_uc -> string -> import:bool -> theory_uc

  val use_export   : theory_uc -> theory -> theory_uc
  val clone_export : theory_uc -> theory -> th_inst -> theory_uc

  val get_namespace : theory_uc -> namespace

  exception CloseTheory
  exception NoOpenedNamespace
  exception ClashSymbol of string

end

(** Debugging *)

val print_ident : Format.formatter -> ident -> unit
val print_uc : Format.formatter -> theory_uc -> unit
val print_ctxt : Format.formatter -> context -> unit
val print_th : Format.formatter -> theory -> unit
