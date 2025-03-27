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

(** Typing parse trees *)

(** {1 Typing parse trees} *)

val debug_parse_only : Debug.flag

val debug_type_only : Debug.flag

val warn_useless_at : Loc.warning_id

val type_mlw_file : Env.env -> string list -> string -> Ptree.mlw_file -> Pmodule.pmodule Wstdlib.Mstr.t

(** {2 Incremental typing of parsed modules} *)

val open_file : Env.env -> Env.pathname -> unit

val close_file : unit -> Pmodule.pmodule Wstdlib.Mstr.t

val discard_file : unit -> unit

val open_module : ?intf:Ptree.qualid -> Ptree.ident -> unit

val close_module : Loc.position -> unit

val open_scope : Loc.position -> Ptree.ident -> unit

val close_scope : Loc.position -> import:bool -> unit

val add_decl : Loc.position -> Ptree.decl -> unit

(** {2 Typing terms and formulas in isolation} *)

val string_list_of_qualid : Ptree.qualid -> string list

val print_qualid : Format.formatter -> Ptree.qualid -> unit

val type_term_in_namespace :
  Theory.namespace -> Decl.known_map -> Coercion.t -> Ptree.term -> Term.term

val type_fmla_in_namespace :
  Theory.namespace -> Decl.known_map -> Coercion.t -> Ptree.term -> Term.term

val type_expr_in_muc :
  Pmodule.pmodule_uc -> ?denv:Dexpr.denv -> Ptree.expr -> Expr.expr

module Unsafe : sig
  val dexpr : Pmodule.pmodule_uc -> Dexpr.denv -> Ptree.expr -> Dexpr.dexpr
  val drec_defn : Pmodule.pmodule_uc -> Dexpr.denv -> Ptree.fundef list -> Dexpr.denv * Dexpr.drec_defn

  val add_decl : Pmodule.pmodule_uc -> Env.env -> Pmodule.pmodule Wstdlib.Mstr.t -> Ptree.decl -> Pmodule.pmodule_uc
  val create_user_id : Ptree.ident -> Ident.preid
  val create_user_prog_id : Ptree.ident -> Ident.preid
end


(** exported for Coma *)

val ty_of_pty : Theory.theory_uc -> Ptree.pty -> Ty.ty

val type_term_in_denv :
  Theory.namespace -> Decl.known_map -> Coercion.t -> Dterm.denv -> Ptree.term -> Term.term

val check_term_in_denv :
  Theory.namespace -> Decl.known_map -> Coercion.t -> Dterm.denv -> Ptree.term -> Ty.ty -> Term.term

val type_fmla_in_denv :
  Theory.namespace -> Decl.known_map -> Coercion.t -> Dterm.denv -> Ptree.term -> Term.term
