(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

(** Typing environments *)

open Util
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

val close_namespace :
  Loc.position -> bool -> string -> theory_uc -> theory_uc

val close_theory : theory Mstr.t -> theory_uc -> theory Mstr.t

val open_file : unit Env.library -> Env.pathname -> Ptree.incremental

val close_file : unit -> theory Mstr.t

(******************************************************************************)
(** The following is exported for program typing (src/programs/pgm_typing.ml) *)
(******************************************************************************)

val specialize_lsymbol :
  Ptree.qualid -> theory_uc -> lsymbol * Denv.dty list * Denv.dty option

val specialize_fsymbol :
  Ptree.qualid -> theory_uc -> lsymbol * Denv.dty list * Denv.dty

val specialize_psymbol :
  Ptree.qualid -> theory_uc -> lsymbol * Denv.dty list

val specialize_tysymbol :
  Loc.position -> Ptree.qualid -> theory_uc -> Ty.tysymbol

val create_user_tv: string -> tvsymbol
val create_user_type_var : string -> Denv.dty

type denv

val denv_empty : denv
val denv_empty_with_globals : (Ptree.qualid -> vsymbol option) -> denv

val mem_var : string -> denv -> bool
val find_var : string -> denv -> Denv.dty
val add_var : string -> Denv.dty -> denv -> denv

val type_term : theory_uc -> denv -> vsymbol Mstr.t -> Ptree.lexpr -> term
val type_fmla : theory_uc -> denv -> vsymbol Mstr.t -> Ptree.lexpr -> term

val dty : theory_uc -> Ptree.pty -> Denv.dty
val dterm : ?localize:(Ptree.loc option option) ->
  theory_uc -> denv -> Ptree.lexpr -> Denv.dterm
val dfmla : ?localize:(Ptree.loc option option) ->
  theory_uc -> denv -> Ptree.lexpr -> Denv.dfmla
val dpat : theory_uc -> denv -> Ptree.pattern -> denv * Denv.dpattern
val dpat_list :
  theory_uc -> denv -> Denv.dty -> Ptree.pattern -> denv * Denv.dpattern

val print_denv : Format.formatter -> denv -> unit
val print_qualid: Format.formatter -> Ptree.qualid -> unit

val split_qualid : Ptree.qualid -> string list * string
val string_list_of_qualid : string list -> Ptree.qualid -> string list
val qloc : Ptree.qualid -> Loc.position

(*
val is_projection : theory_uc -> lsymbol -> (tysymbol * lsymbol * int) option
  (** [is_projection uc ls] returns
      - [Some (ts, lsc, i)] if [ls] is the i-th projection of an
        algebraic datatype [ts] with only one constructor [lcs]
      - [None] otherwise *)

val list_fields: theory_uc ->
  (Ptree.qualid * 'a) list -> tysymbol * lsymbol * (Ptree.loc * 'a) option list
  (** check that the given fields all belong to the same record type
      and do not appear several times *)
*)

val type_inst: theory_uc -> theory -> Ptree.clone_subst list -> th_inst
