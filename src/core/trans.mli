(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ty
open Term
open Decl
open Theory
open Task
open Stdlib

(** Task transformation *)

type 'a trans
type 'a tlist = 'a list trans

val store : (task -> 'a) -> 'a trans
val apply : 'a trans -> (task -> 'a)

val identity   : task trans
val identity_l : task tlist

val singleton : 'a trans -> 'a tlist
val return    : 'a -> 'a trans
val bind      : 'a trans -> ('a -> 'b trans) -> 'b trans

val trace_goal : string -> task trans -> task trans

(** Compose transformation *)
val compose   : task trans -> 'a trans -> 'a trans
val compose_l : task tlist -> 'a tlist -> 'a tlist

val seq   : task trans list -> task trans
val seq_l : task tlist list -> task tlist

(** Create Transformation *)
val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
val fold_l : (task_hd -> 'a -> 'a list) -> 'a -> 'a tlist

val fold_map   : (task_hd -> 'a * 'b -> ('a * 'b)     ) -> 'a -> 'b -> 'b trans
val fold_map_l : (task_hd -> 'a * 'b -> ('a * 'b) list) -> 'a -> 'b -> 'b tlist

(** [decl f acc [d1;..;dn]] returns acc@f d1@..@f dn *)
val decl   : (decl -> decl list     ) -> task -> task trans
val decl_l : (decl -> decl list list) -> task -> task tlist

val tdecl   : (decl -> tdecl list     ) -> task -> task trans
val tdecl_l : (decl -> tdecl list list) -> task -> task tlist

val goal   : (prsymbol -> term -> decl list     ) -> task trans
val goal_l : (prsymbol -> term -> decl list list) -> task tlist

val tgoal   : (prsymbol -> term -> tdecl list     ) -> task trans
val tgoal_l : (prsymbol -> term -> tdecl list list) -> task tlist

val rewrite : (term -> term) -> task -> task trans
val rewriteTF : (term -> term) -> (term -> term) -> task -> task trans

val add_decls  : decl list -> task trans
val add_tdecls : tdecl list -> task trans

(* Dependent Transformations *)

val on_meta : meta -> (meta_arg list list -> 'a trans) -> 'a trans
val on_theory : theory -> (symbol_map list -> 'a trans) -> 'a trans

val on_meta_excl : meta -> (meta_arg list option -> 'a trans) -> 'a trans
val on_used_theory : theory -> (bool -> 'a trans) -> 'a trans

val on_tagged_ty : meta -> (Sty.t -> 'a trans) -> 'a trans
val on_tagged_ts : meta -> (Sts.t -> 'a trans) -> 'a trans
val on_tagged_ls : meta -> (Sls.t -> 'a trans) -> 'a trans
val on_tagged_pr : meta -> (Spr.t -> 'a trans) -> 'a trans

(* Flag-dependent Transformations *)

exception UnknownFlagTrans of meta * string * string list
exception IllegalFlagTrans of meta

type ('a,'b) flag_trans = ('a -> 'b trans) Hstr.t

val on_flag : meta -> ('a,'b) flag_trans -> string -> 'a -> 'b trans
(** [on_flag m ft def arg] takes an exclusive meta [m] of type [[MTstring]],
    a hash table [ft], a default flag value [def], and an argument [arg].
    Returns a transformation that is associated in [ft] to the value of [m]
    in a given task. If the meta [m] is not set in the task, returns the
    transformation associated to [def]. Raises [UnknownFlagTrans] if [ft]
    does not have a requested association. Raises [IllegalFlagTrans] if
    the type of [m] is not [[MTstring]]. *)

(** Debug Transformations *)

val print_meta : Debug.flag -> meta -> task trans
(** [print_meta f m] is an identity transformation that
    prints every meta [m] in the task if flag [d] is set *)

(* Creates new transformation that prints the goal of the task to be 
transfromed, do the original transformation and than prints the goal 
of the transformed task.  *)
val create_debugging_trans: string -> task trans ->  task trans

(** {2 Registration} *)

exception TransFailure of string * exn
exception UnknownTrans of string
exception KnownTrans of string

val register_env_transform   :
  desc:Pp.formatted -> string -> (Env.env -> task trans) -> unit

val register_env_transform_l :
  desc:Pp.formatted -> string -> (Env.env -> task tlist) -> unit

val register_transform   : desc:Pp.formatted -> string -> task trans -> unit
val register_transform_l : desc:Pp.formatted -> string -> task tlist -> unit

val lookup_transform   : string -> Env.env -> task trans
val lookup_transform_l : string -> Env.env -> task tlist

val list_transforms   : unit -> (string * Pp.formatted) list
val list_transforms_l : unit -> (string * Pp.formatted) list

val named : string -> 'a trans -> 'a trans
(** give transformation a name without registering *)

val apply_transform : string -> Env.env -> task -> task list
(** apply a registered 1-to-1 or a 1-to-n function directly *)
