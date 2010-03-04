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

(** Theory *)

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
  | Linductive of lsymbol * (ident * fmla) list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * ident * fmla

(* smart constructors *)

val make_fs_defn : lsymbol -> vsymbol list -> term -> fs_defn
val make_ps_defn : lsymbol -> vsymbol list -> fmla -> ps_defn

val open_fs_defn : fs_defn -> lsymbol * vsymbol list * term
val open_ps_defn : ps_defn -> lsymbol * vsymbol list * fmla

val fs_defn_axiom : fs_defn -> fmla
val ps_defn_axiom : ps_defn -> fmla

module Mnm : Map.S with type key = string

type theory = private {
  th_name   : ident;
  th_local  : Sid.t;        (* locally declared abstract symbols *)
  th_export : namespace;
  th_ctxt   : context;
}

and context = private {
  ctxt_tag   : int;
  ctxt_known : decl Mid.t;  (* imported and locally declared symbols *)
  ctxt_decls : (decl * context) option;
}

and decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_decl
  | Duse of theory
  | Dclone of (ident * ident) list

and decl = private {
  d_node : decl_node;
  d_tag  : int;
}

and namespace = private {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
  ns_pr : fmla Mnm.t;       (* propositions *)
}

val create_type : ty_decl list -> decl
val create_logic : logic_decl list -> decl
val create_prop : prop_kind -> preid -> fmla -> decl

(* exceptions *)

exception ConstructorExpected of lsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of ident

exception IllegalConstructor of lsymbol
exception UnboundVars of Svs.t
exception BadDecl of ident

(* context *)

module Context : sig

  val add_decl : context -> decl -> context

  val iter : (decl -> unit) -> context -> unit
    (** bottom-up, tail-rec *)
  val fold_left : ('a -> decl -> 'a) -> 'a -> context -> 'a
    (** bottom-up, tail-rec *)
    
end

(* theory construction *)

type theory_uc  (* a theory under construction *)

val create_theory : preid -> theory_uc

val close_theory : theory_uc -> theory

val open_namespace : theory_uc -> theory_uc

val close_namespace : theory_uc -> string -> import:bool -> theory_uc

val add_decl : theory_uc -> decl -> theory_uc

val use_export : theory_uc -> theory -> theory_uc

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_ls : lsymbol  Mls.t;
}

val clone_export : theory_uc -> theory -> th_inst -> theory_uc

val get_namespace : theory_uc -> namespace

(* exceptions *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception CannotInstantiate of ident
exception ClashSymbol of string

(** Debugging *)

val print_uc : Format.formatter -> theory_uc -> unit
val print_th : Format.formatter -> theory -> unit
