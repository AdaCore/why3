(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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

val prio_binop: binop -> int

val protect_on: bool -> ('a, 'b, 'c, 'd, 'e, 'f) format6 ->
  ('a, 'b, 'c, 'd, 'e, 'f) format6

type syntax =
| Is_array of string
| Is_getter of string
| Is_none

val get_element_syntax: attrs:Sattr.t -> syntax

module type Printer = sig

    val tprinter : ident_printer  (* type symbols *)
    val aprinter : ident_printer  (* type variables *)
    val sprinter : ident_printer  (* variables and functions *)
    val pprinter : ident_printer  (* proposition names *)

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
    val print_term : formatter -> term -> unit   (* term *)

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

type any_pp =
  | Pp_term of (Term.term * int) (* Term and priority *)
  | Pp_ty of (Ty.ty * int * bool) (* ty * prio * q *)
  | Pp_decl of (bool * Ty.tysymbol * (Term.lsymbol * Term.lsymbol option list) list)
    (* [Pp_decl (fst, ts, csl)]: Declaration of type [ts] with constructors
       [csl] as [fst] *)
  | Pp_ts of Ty.tysymbol (* Print tysymbol *)
  | Pp_ls of Term.lsymbol (* Print lsymbol *)
  | Pp_id of Ident.ident (* Print ident *)
  | Pp_cs of Term.lsymbol (* Print constructors *)
  | Pp_vs of Term.vsymbol (* Print vsymbol *)
  | Pp_trigger of Term.trigger (* Print triggers *)
  | Pp_forget of Term.vsymbol list (* Forget all the vsymbols listed *)
  | Pp_forget_tvs (* execute forget_tvs *)


val create :
  ?print_ext_any:(any_pp Pp.pp -> any_pp Pp.pp) ->
  Ident.ident_printer -> Ident.ident_printer ->
  Ident.ident_printer -> Ident.ident_printer ->
  bool -> (module Printer)
(** `create spr apr tpr ppr forget` creates a new pretty-printing
   module from the printer `spr` for variables and functions, `apr`
   for type variables, `tpr` for type symbols and `ppr for proposition
   names`. When the Boolean `forget` is true then all recorded names
   are forgotten between printing of each tasks. *)
