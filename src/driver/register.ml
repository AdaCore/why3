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

open Task
open Trans
open Driver

type use   = Theory.use_map
type clone = Theory.clone_map
type query = driver_query

type 'a value = Env.env option -> driver option -> task -> 'a

type 'a trans_reg = {
  mutable value    : 'a value;
          generate : unit -> 'a value;
}

type 'a tlist_reg = 'a list trans_reg

let create gen = {
  value    = gen ();
  generate = gen;
}

module WHenv = Hashweak.Make (struct
  type t = Env.env
  let tag = Env.env_tag
end)

module WHquery = Hashweak.Make (struct
  type t = driver_query
  let tag = query_tag
end)

module WHtask = Hashweak.Make (struct
  type t = task_hd
  let tag t = t.task_tag
end)

exception ArgumentNeeded

let memo_env fn =
  let fn = WHenv.memoize 7 fn in function
    | None -> raise ArgumentNeeded
    | Some env -> fn env

let memo_query fn =
  let fn = WHquery.memoize 7 fn in function
    | None -> raise ArgumentNeeded
    | Some drv -> fun task -> fn (driver_query drv task)

let memo_use fn =
  let fn task = fn (task_used task) in
  let fn = WHtask.memoize_option 63 fn in
  fun task -> fn (last_use task)

let memo_clone fn =
  let fn task = fn (task_clone task) in
  let fn = WHtask.memoize_option 63 fn in
  fun task -> fn (last_clone task)

let memo_goal fn = WHtask.memoize_option 7 fn

let gen_task f () =
  let f0 = Trans.apply (f ()) in
  fun _ _ task -> f0 task

let gen_env f () =
  let f0 env = Trans.apply (f env) in
  let f1 = memo_env f0 in
  fun env _ task -> f1 env task

let gen_query f () =
  let f0 query = Trans.apply (f query) in
  let f1 = memo_query f0 in
  fun _ drv task -> f1 drv task task

let gen_arg memo_arg f () =
  let f0 env arg = Trans.apply (f env arg) in
  let f1 env = memo_arg (f0 env) in
  let f2 = memo_env f1 in
  fun env _ task -> f2 env task task

let gen_full f () =
  let f0 query goal = Trans.apply (f query goal) in
  let f1 query = memo_goal (f0 query) in
  let f2 = memo_query f1 in
  fun _ drv task -> f2 drv task task task

let gen_both f () =
  let f0 env use clone = Trans.apply (f env use clone) in
  let f1 env use = memo_clone (f0 env use) in
  let f2 env = memo_use (f1 env) in
  let f3 = memo_env f2 in
  fun env _ task -> f3 env task task task

let store       f = create (gen_task f)
let store_env   f = create (gen_env f)
let store_goal  f = create (gen_arg memo_goal f)
let store_clone f = create (gen_arg memo_clone f)
let store_use   f = create (gen_arg memo_use f)
let store_both  f = create (gen_both f)
let store_query f = create (gen_query f)
let store_full  f = create (gen_full f)

let apply reg = reg.value None None
let apply_env reg env = reg.value (Some env) None
let apply_driver reg drv = reg.value (Some (get_env drv)) (Some drv)

let clear reg = reg.value <- reg.generate ()

let conv_res conv reg1 =
  let app f env drv task = conv (f env drv task) in
  let gen () = app (reg1.generate ()) in
  { value = app reg1.value; generate = gen }

let combine comb reg1 reg2 =
  let app f1 f2 env drv = comb (f1 env drv) (f2 env drv) in
  let gen () = app (reg1.generate ()) (reg2.generate ()) in
  { value = app reg1.value reg2.value; generate = gen }

let singleton reg = conv_res (fun x -> [x]) reg

let identity   = store (fun () -> Trans.identity)
let identity_l = store (fun () -> Trans.identity_l)

let compose   r1 r2 = combine (fun t1 t2 x -> t2 (t1 x)) r1 r2
let compose_l r1 r2 = combine (fun t1 t2 x -> Util.list_apply t2 (t1 x)) r1 r2

(** register printers and transformations *)

type printer = query -> Format.formatter -> task -> unit

let printers     : (string, printer)        Hashtbl.t = Hashtbl.create 17
let transforms   : (string, task trans_reg) Hashtbl.t = Hashtbl.create 17
let transforms_l : (string, task tlist_reg) Hashtbl.t = Hashtbl.create 17

let register_printer     = Hashtbl.replace printers
let register_transform   = Hashtbl.replace transforms
let register_transform_l = Hashtbl.replace transforms_l

let lookup_printer       = Hashtbl.find printers
let lookup_transform     = Hashtbl.find transforms
let lookup_transform_l   = Hashtbl.find transforms_l

let list_printers ()     = Hashtbl.fold (fun k _ acc -> k::acc) printers []
let list_transforms ()   = Hashtbl.fold (fun k _ acc -> k::acc) transforms []
let list_transforms_l () = Hashtbl.fold (fun k _ acc -> k::acc) transforms_l []

(** exception to use in a printer and transformation *)

open Ty
open Term
open Decl

type error =
  | UnsupportedType of ty   * string
  | UnsupportedExpr of expr * string
  | UnsupportedDecl of decl * string
  | NotImplemented  of        string

exception Error of error

let error e = raise (Error e)

let unsupportedType e s = error (UnsupportedType (e,s))
let unsupportedTerm e s = error (UnsupportedExpr (Term e,s))
let unsupportedFmla e s = error (UnsupportedExpr (Fmla e,s))
let unsupportedExpr e s = error (UnsupportedExpr (e,s))
let unsupportedDecl e s = error (UnsupportedDecl (e,s))
let notImplemented    s = error (NotImplemented s)

let report fmt = function
  | UnsupportedType (e,s) ->
      let msg = "This type isn't supported" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_ty e s
  | UnsupportedExpr (e,s) ->
      let msg = "This expression isn't supported" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_expr e s
  | UnsupportedDecl (d,s) ->
      let msg = "This declaration isn't supported" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_decl d s
  | NotImplemented (s) ->
      Format.fprintf fmt "@[<hov 3> Unimplemented feature:@\n%s@]@\n" s

(** function which cath inner error *)
exception Unsupported of string

let unsupported s = raise (Unsupported s)

let catch_unsupportedType f e =
  try f e with Unsupported s -> unsupportedType e s

let catch_unsupportedTerm f e =
  try f e with Unsupported s -> unsupportedTerm e s

let catch_unsupportedFmla f e =
  try f e with Unsupported s -> unsupportedFmla e s

let catch_unsupportedExpr f e =
  try f e with Unsupported s -> unsupportedExpr e s

let catch_unsupportedDecl f e =
  try f e with Unsupported s -> unsupportedDecl e s

