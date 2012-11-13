(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Typing environments *)

open Stdlib
open Ty
open Term
open Theory

val debug_parse_only : Debug.flag
val debug_type_only : Debug.flag

(** incremental parsing *)

val add_decl : Loc.position -> theory_uc -> Ptree.decl -> theory_uc

val add_use_clone :
  unit Env.library -> theory Mstr.t -> theory_uc ->
    Loc.position -> Ptree.use_clone -> theory_uc

val close_namespace : Loc.position -> bool -> theory_uc -> theory_uc

val close_theory : theory Mstr.t -> theory_uc -> theory Mstr.t

val open_file : unit Env.library -> Env.pathname -> Ptree.incremental

val close_file : unit -> theory Mstr.t

(***************************************************************************)
(** The following is exported for program typing (src/whyml/mlw_typing.ml) *)
(***************************************************************************)

val create_user_tv : string -> tvsymbol

val print_qualid : Format.formatter -> Ptree.qualid -> unit
val split_qualid : Ptree.qualid -> string list * string
val qloc : Ptree.qualid -> Loc.position

val find_ns :
  ('a -> Ident.ident) -> ('b -> string list -> 'a) -> Ptree.qualid -> 'b -> 'a

val type_term :
  theory_uc -> (Ptree.qualid -> vsymbol option) -> Ptree.lexpr -> term

val type_fmla :
  theory_uc -> (Ptree.qualid -> vsymbol option) -> Ptree.lexpr -> term

val type_inst : theory_uc -> theory -> Ptree.clone_subst list -> th_inst
