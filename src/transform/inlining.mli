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


(** Inline the definitions not recursive *)

val meta : Theory.meta

(** {2 Generic inlining} *)

val t :
  ?use_meta:bool ->
  notdeft:(Term.term -> bool) ->
  notdeff:(Term.fmla -> bool) ->
  notls  :(Term.lsymbol -> bool) ->
  Task.task Trans.trans
(** [t ~use_meta ~notdeft ~notdeff ~notls] returns a transformation which
    inlines a symbol definition in the other definitions and propositions when
    it verifies this condition :
    [CLAUDE: C'EST UN ou OU UN et DE CES CONDITIONS ??]
    - Its definitions doesn't verify [notdeft] in case of a logic function or
    [notdeff] in case of a predicate
    - Its logic symbol doesn't verify [notls]
    - use_meta is not set or its logic symbol is not tagged by "inline : not"

    Notice that [use_meta], [notdeft], [notdeff], [notls] restrict only which
    symbols are inlined not when.
*)

(** {2 Registered Transformation} *)

val all : Task.task Trans.trans
(** [all] corresponds to the transformation "inline_all" *)



val trivial : Task.task Trans.trans
(** [trivial] corresponds to the transformation "inline_trivial"
    Inline only the trivial definition :
    logic c : t = a
    logic f(x : t,...., ) : t = g(y : t2,...) *)

(** Functions to use in other transformations if inlining is needed *)

type env

val empty_env : env

val addfs : env -> Term.lsymbol -> Term.vsymbol list -> Term.term -> env
val addps : env -> Term.lsymbol -> Term.vsymbol list -> Term.fmla -> env
(** [addls env ls vs t] trigger the inlining of [ls] by the definition
    [t] with the free variables [vs]. The variables of [vs] must have
    the type of the arguments of [ls] *)

val replacet : env -> Term.term -> Term.term
val replacep : env -> Term.fmla -> Term.fmla
