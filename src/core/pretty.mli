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

(** Pretty-printing various objects from Why3's core logic *)

val coercion_attr : Ident.attribute

val why3_keywords : string list

open Format
open Ident
open Ty
open Term
open Decl
open Theory
open Task

module type Printer = sig

    val tprinter : ident_printer  (* type symbols *)
    val aprinter : ident_printer  (* type variables *)
    val sprinter : ident_printer  (* variables and functions *)
    val pprinter : ident_printer  (* propoition names *)

    val forget_all : unit -> unit     (* flush id_unique *)
    val forget_tvs : unit -> unit     (* flush id_unique for type vars *)
    val forget_var : vsymbol -> unit  (* flush id_unique for a variable *)

    val print_id_attrs : formatter -> ident -> unit   (* attributes and location *)

    val print_tv : formatter -> tvsymbol -> unit      (* type variable *)
    val print_vs : formatter -> vsymbol -> unit       (* variable *)

    val print_ts : formatter -> tysymbol -> unit      (* type symbol *)
    val print_ls : formatter -> lsymbol -> unit       (* logic symbol *)
    val print_cs : formatter -> lsymbol -> unit       (* constructor symbol *)
    val print_pr : formatter -> prsymbol -> unit      (* proposition name *)
    val print_th : formatter -> theory -> unit        (* theory name *)

    val print_ty : formatter -> ty -> unit            (* type *)
    val print_vsty : formatter -> vsymbol -> unit     (* variable : type *)

    val print_ts_qualified : formatter -> tysymbol -> unit
    val print_ls_qualified : formatter -> lsymbol -> unit
    val print_cs_qualified : formatter -> lsymbol -> unit
    val print_pr_qualified : formatter -> prsymbol -> unit
    val print_th_qualified : formatter -> theory -> unit
    val print_ty_qualified : formatter -> ty -> unit

    val print_quant : formatter -> quant -> unit      (* quantifier *)
    val print_binop : asym:bool -> formatter -> binop -> unit (* binary operator *)
    val print_pat : formatter -> pattern -> unit      (* pattern *)
    val print_term : formatter -> term -> unit        (* term *)

    val print_attr : formatter -> attribute -> unit
    val print_loc : formatter -> Loc.position -> unit
    val print_pkind : formatter -> prop_kind -> unit
    val print_meta_arg : formatter -> meta_arg -> unit
    val print_meta_arg_type : formatter -> meta_arg_type -> unit

    val print_ty_decl : formatter -> tysymbol -> unit
    val print_data_decl : formatter -> data_decl -> unit
    val print_param_decl : formatter -> lsymbol -> unit
    val print_logic_decl : formatter -> logic_decl -> unit
    val print_ind_decl : formatter -> ind_sign -> ind_decl -> unit
    val print_next_data_decl : formatter -> data_decl -> unit
    val print_next_logic_decl : formatter -> logic_decl -> unit
    val print_next_ind_decl : formatter -> ind_decl -> unit
    val print_prop_decl : formatter -> prop_decl -> unit

    val print_decl : formatter -> decl -> unit
    val print_tdecl : formatter -> tdecl -> unit

    val print_task : formatter -> task -> unit
    val print_sequent : formatter -> task -> unit

    val print_theory : formatter -> theory -> unit

    val print_namespace : formatter -> string -> theory -> unit

  end

include Printer

val create :  Ident.ident_printer -> Ident.ident_printer ->
              Ident.ident_printer -> Ident.ident_printer ->
              bool -> (module Printer)
