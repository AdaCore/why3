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

(** Typing environments *)

open Wstdlib
open Term
open Theory

val debug_parse_only : Debug.flag
val debug_type_only : Debug.flag

(** incremental parsing *)

val add_range_decl :
  'a ->
  ('a -> Decl.decl -> 'a) ->
  ('a -> Theory.meta -> Theory.meta_arg list -> 'a) ->
  Ty.tysymbol -> Number.int_range -> 'a

val add_float_decl:
  'a ->
  ('a -> Decl.decl -> 'a) ->
  ('a -> Theory.meta -> Theory.meta_arg list -> 'a) ->
  Ty.tysymbol -> Number.float_format -> 'a

val add_decl : Loc.position -> theory_uc -> Ptree.decl -> theory_uc

val add_use_clone :
  Env.env -> theory Mstr.t -> theory_uc ->
    Loc.position -> Ptree.use_clone -> theory_uc

val close_namespace : Loc.position -> bool -> theory_uc -> theory_uc

val close_theory : theory Mstr.t -> theory_uc -> theory Mstr.t

val open_file : Env.env -> Env.pathname -> Ptree.incremental

val close_file : unit -> theory Mstr.t

(***************************************************************************)
(** The following is exported for program typing (src/whyml/mlw_typing.ml) *)
(***************************************************************************)

val create_user_id : Ptree.ident -> Ident.preid

val qloc : Ptree.qualid -> Loc.position
val string_list_of_qualid : Ptree.qualid -> string list
val print_qualid : Format.formatter -> Ptree.qualid -> unit

exception UnboundSymbol of Ptree.qualid

val find_qualid :
  ('a -> Ident.ident) -> ('b -> string list -> 'a) -> 'b -> Ptree.qualid -> 'a

type global_vs = Ptree.qualid -> vsymbol option

val type_term : theory_uc -> global_vs -> Ptree.term -> term

val type_fmla : theory_uc -> global_vs -> Ptree.term -> term

val type_inst : theory_uc -> theory -> Ptree.clone_subst list -> th_inst
