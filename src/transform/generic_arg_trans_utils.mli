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

open Term

exception Arg_trans of string
exception Arg_trans_decl of (string * Theory.tdecl list)
exception Arg_trans_term of (string * term)
exception Arg_trans_term2 of (string * term * term)
exception Arg_trans_term3 of (string * term * term * term)
exception Arg_trans_pattern of (string * pattern * pattern)
exception Arg_trans_type of (string * Ty.ty * Ty.ty)
exception Arg_trans_missing of (string * Svs.t)
exception Arg_bad_hypothesis of (string * term)
exception Cannot_infer_type of string
exception Unnecessary_terms of term list

val gen_ident :
  ?attrs:Ident.Sattr.t -> ?loc:Loc.position -> string -> Ident.preid

val replace_in_term: term -> term -> term -> term

val subst_quant: quant -> term_quant -> term -> term

(* Transform the term (exists v, f) into f[x/v] *)
val subst_exist: term -> term -> term

(* Transform the term (forall v, f) into f[x/v] *)
val subst_forall: term -> term -> term

(* TODO remove subst_forall and subst_exist *)
(* Same as subst_forall with a list of term *)
val subst_forall_list: term -> term list -> term

(* Returns the list of local declarations *)
val get_local: Decl.decl list Trans.trans

val get_local_task: Task.task -> Decl.decl list

(* Returns same list of declarations but reorganized with constant/type
   definitions defined before axioms *)
val sort: Task.task Trans.trans

(*************************)
(* Substitution of terms *)
(*************************)

type term_subst = term Mterm.t

val replace_subst: term_subst -> Term.term -> Term.term

val replace_decl: term_subst -> Decl.decl -> Decl.decl

val replace_tdecl: term_subst -> Theory.tdecl -> Theory.tdecl

(************************)
(* Explanation handling *)
(************************)

(* This function creates a goal with an explanation. The term on which this is
   applied should not contain any explanation itself (otherwise both would
   appear in the ide).
*)
val create_goal: expl:string -> Decl.prsymbol -> Term.term -> Decl.decl
