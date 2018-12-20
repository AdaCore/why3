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

(** Task transformations *)

open Ty
open Term
open Decl
open Theory
open Task
open Wstdlib

(** {2 Transformations} *)

type 'a trans
type 'a tlist = 'a list trans

val store : (task -> 'a) -> 'a trans
val apply : 'a trans -> (task -> 'a)

val identity   : task trans
val identity_l : task tlist

val singleton : 'a trans -> 'a tlist
val return    : 'a -> 'a trans
val bind      : 'a trans -> ('a -> 'b trans) -> 'b trans
val bind_comp : ('a * task) trans -> ('a -> 'b trans) -> 'b trans

val trace_goal : string -> task trans -> task trans

(** {2 Compose transformations} *)

val compose   : task trans -> 'a trans -> 'a trans
val compose_l : task tlist -> 'a tlist -> 'a tlist

val seq   : task trans list -> task trans
val seq_l : task tlist list -> task tlist

val par : task trans list -> task tlist
(** parallelize transformations: [par l] will duplicate the current
    task in [n] new tasks, with [n] the length of [l], and apply to each of
    this new task the corresponding transformation in [l] *)

(** {2 Iterating transformations} *)
val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
val fold_l : (task_hd -> 'a -> 'a list) -> 'a -> 'a tlist
val fold_decl : (decl -> 'a -> 'a     ) -> 'a -> 'a trans

val fold_map   : (task_hd -> 'a * 'b -> ('a * 'b)     ) -> 'a -> 'b -> 'b trans
val fold_map_l : (task_hd -> 'a * 'b -> ('a * 'b) list) -> 'a -> 'b -> 'b tlist

val decl   : (decl -> decl list     ) -> task -> task trans
(** [decl f t1 t2] appends to task [t1] the set of declarations [f d]
    for each declaration [d] of task [t2], similarly to a "flat_map"
    operation on lists.

    For example, if [t2] is made of the two declarations [d1] and [d2]
    in that order, if [f d1 = [d11;d12]] and [f d2 = [d21;d22]], then
    the resulting task contains the declarations of [t1] followed by
    [d11;d12;d21;d22] *)

val decl_l : (decl -> decl list list) -> task -> task tlist
(** [decl_f f t1 t2] produces a set of tasks obtained by appending new
    declarations to task [t1].  It iterates on each declaration [d]
    appearing in [t2]: if [f d = [ld_1; ld_2; ... ld_n]] then it
    produces [n] tasks [t'1;..;t'n], where [ld_i] is appended to [t'i].
    The operation on remaining tasks of [t2] are then applied to each task [t'i].

    For example, if [t2] is made of the two declarations [d1] and [d2]
    in that order, if [f d1 = [[d111;d112];[d12]]] and [f d2 =
    [[d21];[d221;d222]]], then the result is made of the 4 tasks
    [t1;d111;d112;d21], [t1;d111;d112;d221;d222], [t1;d12;d21] and
    [t1;d12;d221;d222] *)


type diff_decl =
  | Goal_decl of Decl.decl
  | Normal_decl of Decl.decl
(* FIXME: the differenciation of goal versus normal decl should be made using
  [is_goal d = match d.decl_node with
  | Prop(Goal,_) -> true | _ -> false] *)

val decl_goal_l: (decl -> diff_decl list list) -> task -> task tlist
(** FIXME:
     * make this comment more comprehensible
     * there should be no "disallowed cases": as soon as a goal is produced, no new decls should be added anymore in the resulting tasks


    [decl_goal_l f t1 t2] does the same as decl_l except that it can
    differentiate a new axiom added to a task from a new goal added to a task.
    In case of a new axiom, everything works as in decl_l. When a new goal [ng]
    is generated, it is remembered so that it can replace the old_goal when the
    end of the task is encountered.

    Example of use of this feature in the code of [destruct]:
    H1: p1 -> p2
    H2: p3
    H3: ...
    -------------
    Goal: True

    In [destruct H1], we know that we will add a new goal [p1] before we read
    through the entire task, so we need to be able to generate a new goal.

    Current disallowed cases:
    - Creating a goal twice in the same branch
    - Creating a goal when analysing the goal of [t2]
*)

val tdecl   : (decl -> tdecl list     ) -> task -> task trans
val tdecl_l : (decl -> tdecl list list) -> task -> task tlist

val goal   : (prsymbol -> term -> decl list     ) -> task trans
val goal_l : (prsymbol -> term -> decl list list) -> task tlist

val tgoal   : (prsymbol -> term -> tdecl list     ) -> task trans
val tgoal_l : (prsymbol -> term -> tdecl list list) -> task tlist

val rewrite : (term -> term) -> task -> task trans
(** [rewrite f t1 t2] appends to task [t1] the declarations in [t2]
    in which each top level formula [t] is replaced by [f t] **)
val rewriteTF : (term -> term) -> (term -> term) -> task -> task trans

val add_decls  : decl list -> task trans
val add_tdecls : tdecl list -> task trans
(** [add_decls ld t1] adds decls ld at the end of the task t1 (before the goal) *)

(** {2 Dependent Transformations} *)

val on_meta : meta -> (meta_arg list list -> 'a trans) -> 'a trans
val on_meta_excl : meta -> (meta_arg list option -> 'a trans) -> 'a trans

val on_used_theory : theory -> (bool -> 'a trans) -> 'a trans
val on_cloned_theory : theory -> (symbol_map list -> 'a trans) -> 'a trans

(** [on_tagged_* m f] allow to do a transformation having all the tagged declarations
    in a set as argument of f.
    If used to modify the existing task, be careful to not make references to
    declarations found in the set before they are actually declared in the new task.

    For example, this will likely fail:
      Trans.on_tagged_ls some_meta (fun s -> Trans.decl (fun d -> [d; s.choose]))
*)
val on_tagged_ty : meta -> (Sty.t -> 'a trans) -> 'a trans
val on_tagged_ts : meta -> (Sts.t -> 'a trans) -> 'a trans
val on_tagged_ls : meta -> (Sls.t -> 'a trans) -> 'a trans
val on_tagged_pr : meta -> (Spr.t -> 'a trans) -> 'a trans

(** {2 Flag-dependent Transformations} *)

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

val on_flag_t : meta -> ('a,'b) flag_trans -> ('a -> 'b trans) -> 'a -> 'b trans

(** {2 Debug Transformations} *)

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

(** {2 Transformations with arguments}

  These transformations take strings as arguments. For a more "typed" version,
  see file [src/transform/args_wrapper.ml]

*)

type naming_table = {
    namespace : namespace;
    known_map : known_map;
    coercion : Coercion.t;
    printer : Ident.ident_printer;
    aprinter : Ident.ident_printer;
 }
(** In order to interpret, that is type, string arguments as symbols or
   terms, a transformation may need a [naming_table]. Typing arguments
   requires looking up identifiers into the [namespace] and also
   looking up declarations into the [known_map]. Since the identifiers
   given as arguments come from the task as it is displayed to the
   user, we need to ensure that the names in the [namespace] are
   coherent with the names that are printed, this why we also record
   the [printer].

   See module [Args_wrapper] for the functions that builds objects of
   type [naming_table] from given tasks, and types the arguments of
   transformations.  *)

exception Bad_name_table of string

type trans_with_args = string list -> Env.env -> naming_table -> task trans
type trans_with_args_l = string list -> Env.env -> naming_table -> task tlist

val list_transforms_with_args   : unit -> (string * Pp.formatted) list
val list_transforms_with_args_l : unit -> (string * Pp.formatted) list

val register_transform_with_args   : desc:Pp.formatted -> string -> trans_with_args -> unit
val register_transform_with_args_l : desc:Pp.formatted -> string -> trans_with_args_l -> unit

(** {2 handling of all forms of transformations} *)

type gentrans =
  | Trans_one of Task.task trans
  | Trans_list of Task.task tlist
  | Trans_with_args of trans_with_args
  | Trans_with_args_l of trans_with_args_l

val lookup_trans : Env.env -> string -> gentrans

val lookup_trans_desc: string -> Pp.formatted
(* Takes the name of a transformation (with args or not) and returns its
   description. *)

val list_trans : unit -> string list

val apply_transform : string -> Env.env -> task -> task list
(** apply a registered 1-to-1 or a 1-to-n, directly.*)

val apply_transform_args : string -> Env.env -> string list -> naming_table -> task -> task list
(** apply a registered 1-to-1 or a 1-to-n or a trans with args, directly *)
