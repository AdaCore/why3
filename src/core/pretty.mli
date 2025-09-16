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

(** Pretty-printing various objects from Why3's core logic *)

open Ident
open Ty
open Term
open Decl
open Theory
open Task

val coercion_attr : Ident.attribute
(** Attribute to put on unary functions to make them considered as
   coercions, hence not printed by default. *)

val why3_keywords : string list
(** the list of all WhyML keywords. *)

val prio_binop: binop -> int
(** priorities of each binary operators *)

val protect_on: bool -> ('a, 'b, 'c, 'd, 'e, 'f) format6 ->
  ('a, 'b, 'c, 'd, 'e, 'f) format6
(** add parentheses around when first arugment is true. *)

(** {2 Specific syntax} *)

type syntax =
| Is_array of string
| Is_getter of string
| Is_none

val get_element_syntax: attrs:Sattr.t -> syntax

(** {2 Module type for printers} *)

module type Printer = sig

  val tprinter : ident_printer
  (** printer for identifiers of type symbols *)

  val aprinter : ident_printer
  (** printer for identifiers of type variables *)

  val sprinter : ident_printer
  (** printer for identifiers of variables and functions *)

  val pprinter : ident_printer
  (** printer for identifiers of proposition *)

  val forget_all : unit -> unit
  (** flush id_unique *)

  val forget_tvs : unit -> unit
  (** flush id_unique for type vars *)

  val forget_var : vsymbol -> unit
  (** flush id_unique for a variable *)

  val print_id_attrs : ident Pp.pp
  (** prints attributes and location of an ident (but not the ident itself) *)

  val print_tv : tvsymbol Pp.pp
  val print_vs : vsymbol Pp.pp

  val print_ts : tysymbol Pp.pp
  val print_ls : lsymbol Pp.pp
  val print_cs : lsymbol Pp.pp
  val print_pr : prsymbol Pp.pp
  val print_th : theory Pp.pp

  val print_ty : ty Pp.pp
  val print_vsty : vsymbol Pp.pp
  (** prints ``variable : type'' *)

  val print_ts_qualified : tysymbol Pp.pp
  val print_ls_qualified : lsymbol Pp.pp
  val print_cs_qualified : lsymbol Pp.pp
  val print_pr_qualified : prsymbol Pp.pp
  val print_th_qualified : theory Pp.pp
  val print_ty_qualified : ty Pp.pp
  val print_vs_qualified : vsymbol Pp.pp
  val print_tv_qualified : tvsymbol Pp.pp

  val print_quant : quant Pp.pp
  val print_binop : asym:bool -> binop Pp.pp
  val print_pat : pattern Pp.pp
  val print_term : term Pp.pp

  val print_attr : attribute Pp.pp
  val print_attrs : Sattr.t Pp.pp
  val print_loc_as_attribute : Loc.position Pp.pp
  val print_pkind : prop_kind Pp.pp
  val print_meta_arg : meta_arg Pp.pp
  val print_meta_arg_type : meta_arg_type Pp.pp

  val print_ty_decl : tysymbol Pp.pp
  val print_data_decl : data_decl Pp.pp
  val print_param_decl : lsymbol Pp.pp
  val print_logic_decl : logic_decl Pp.pp
  val print_ind_decl : ind_sign -> ind_decl Pp.pp
  val print_next_data_decl : data_decl Pp.pp
  val print_next_logic_decl : logic_decl Pp.pp
  val print_next_ind_decl : ind_decl Pp.pp
  val print_prop_decl : prop_decl Pp.pp

  val print_decl : decl Pp.pp
  val print_tdecl : tdecl Pp.pp

  val print_task : task Pp.pp
  val print_sequent : task Pp.pp

  val print_theory : theory Pp.pp

  val print_namespace : string -> theory Pp.pp

end

(** {2 The default printer} *)

include Printer

(** {2 Extended pretty-printers} *)

type any_pp =
  | Pp_term of (Term.term * int) (** Term and priority *)
  | Pp_ty of (Ty.ty * int * bool) (** ty * prio * q *)
  | Pp_decl of (bool * Ty.tysymbol * (Term.lsymbol * Term.lsymbol option list) list)
    (** [Pp_decl (fst, ts, csl)]: Declaration of type [ts] with constructors
       [csl] as [fst] *)
  | Pp_ts of Ty.tysymbol (** Print tysymbol *)
  | Pp_ls of Term.lsymbol (** Print lsymbol *)
  | Pp_id of Ident.ident (** Print ident *)
  | Pp_cs of Term.lsymbol (** Print constructors *)
  | Pp_vs of Term.vsymbol (** Print vsymbol *)
  | Pp_trigger of Term.trigger (** Print triggers *)
  | Pp_forget of Term.vsymbol list (** Forget all the vsymbols listed *)
  | Pp_forget_tvs (** execute forget_tvs *)


val create :
  ?print_ext_any:(any_pp Pp.pp -> any_pp Pp.pp) ->
  ?do_forget_all:bool ->
  ?shorten_axioms:bool ->
  ?show_uses_clones_metas:bool ->
  Ident.ident_printer -> Ident.ident_printer ->
  Ident.ident_printer -> Ident.ident_printer ->
  (module Printer)
(** [create spr apr tpr ppr] creates a new pretty-printing module from
   the printer [spr] for variables and functions, [apr] for type
   variables, [tpr] for type symbols and [ppr] for proposition names.
   If [do_forget_all] is true (default), then all recorded names are
   forgotten between printing of each tasks.  If [shorten_axioms] is
   false (default), axioms are prefixed by the keyword.  If
   [show_uses_clones_metas] is true (default), displays in comments
   the declarations of used and cloned theories, and metas. *)
