(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Ty
open Term
open Decl
open Theory
open Task

(** Task transformation *)

type 'a trans
type 'a tlist = 'a list trans

val store : (task -> 'a) -> 'a trans
val apply : 'a trans -> (task -> 'a)

val identity   : task trans
val identity_l : task tlist

val singleton : 'a trans -> 'a tlist
val return    : 'a -> 'a trans

(** Compose transformation *)
val compose   : task trans -> 'a trans -> 'a trans
val compose_l : task tlist -> 'a tlist -> 'a tlist

val seq   : task trans list -> task trans
val seq_l : task tlist list -> task tlist

(** Create Transformation *)
val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
val fold_l : (task_hd -> 'a -> 'a list) -> 'a -> 'a tlist

val fold_map   : (task_hd -> 'a * task -> ('a * task)) ->
                                      'a -> task -> task trans

val fold_map_l : (task_hd -> 'a * task -> ('a * task) list) ->
                                      'a -> task -> task tlist

val decl   : (decl -> decl list     ) -> task -> task trans
(** [decl f acc [d1;..;dn]] returns acc@f d1@..@f dn *)
val decl_l : (decl -> decl list list) -> task -> task tlist

val tdecl   : (decl -> tdecl list     ) -> task -> task trans
val tdecl_l : (decl -> tdecl list list) -> task -> task tlist

val goal   : (prsymbol -> fmla -> decl list     ) -> task trans
val goal_l : (prsymbol -> fmla -> decl list list) -> task tlist

val tgoal   : (prsymbol -> fmla -> tdecl list     ) -> task trans
val tgoal_l : (prsymbol -> fmla -> tdecl list list) -> task tlist

val rewrite : (term -> term) -> (fmla -> fmla) -> task -> task trans

val add_decls  : decl list -> task trans
val add_tdecls : tdecl list -> task trans

(* dependent transformatons *)

val on_meta : meta -> (meta_arg list list -> 'a trans) -> 'a trans
val on_theory : theory -> (symbol_map list -> 'a trans) -> 'a trans

val on_meta_excl : meta -> (meta_arg list option -> 'a trans) -> 'a trans
val on_used_theory : theory -> (bool -> 'a trans) -> 'a trans

val on_tagged_ty : meta -> (Sty.t -> 'a trans) -> 'a trans
val on_tagged_ts : meta -> (Sts.t -> 'a trans) -> 'a trans
val on_tagged_ls : meta -> (Sls.t -> 'a trans) -> 'a trans
val on_tagged_pr : meta -> (Spr.t -> 'a trans) -> 'a trans

(** debug transformation *)
val print_meta : Debug.flag -> meta -> task trans
(** [print_meta f m] is an identity transformation that
    prints every meta [m] in the task if flag [d] is set *)

(** {2 Registration} *)

exception TransFailure of (string * exn)
exception UnknownTrans of string
exception KnownTrans of string

val register_env_transform   : string -> (Env.env -> task trans) -> unit
val register_env_transform_l : string -> (Env.env -> task tlist) -> unit

val register_transform   : string -> task trans -> unit
val register_transform_l : string -> task tlist -> unit

val lookup_transform   : string -> Env.env -> task trans
val lookup_transform_l : string -> Env.env -> task tlist

val list_transforms   : unit -> string list
val list_transforms_l : unit -> string list

val named : string -> 'a trans -> 'a trans
(** give transformation a name without registering *)

(** {3 Private Registration} *)
(** Can be used for chosing a transformation from a meta *)


type ('a,'b) private_register = private
    { pr_meta : meta;
      pr_default : string;
      pr_table : (string,'a -> 'b trans) Hashtbl.t}

type empty
 (* A type without value, an (empty,empty) private_register can't be used. *)

exception UnknownTransPrivate of (empty,empty) private_register * string

val create_private_register :
  string -> string -> ('a, 'b) private_register
(** [create_provate_register meta_name default] *)

val private_register_env :
  ('a, 'b) private_register -> string -> ('a -> 'b trans) -> unit

val private_register :
  (unit, 'b) private_register -> string -> 'b trans -> unit

val apply_private_register_env :
  ('a, 'b) private_register -> 'a -> 'b trans

val apply_private_register :
  (unit, 'b) private_register -> 'b trans
