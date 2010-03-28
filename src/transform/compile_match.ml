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

open Term
open Decl
open Task

let rec rewriteT kn t = match t.t_node with
  | Tcase (tl,bl) ->
      let tl = List.map (rewriteT kn) tl in
      let mk_b (pl,t) = (pl, rewriteT kn t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      Pattern.CompileTerm.compile (find_constructors kn) tl bl
  | _ -> t_map (rewriteT kn) (rewriteF kn) t

and rewriteF kn f = match f.f_node with
  | Fcase (tl,bl) ->
      let tl = List.map (rewriteT kn) tl in
      let mk_b (pl,f) = (pl, rewriteF kn f) in
      let bl = List.map (fun b -> mk_b (f_open_branch b)) bl in
      Pattern.CompileFmla.compile (find_constructors kn) tl bl
  | _ -> f_map (rewriteT kn) (rewriteF kn) f

let comp t task =
  let fnT = rewriteT t.task_known in
  let fnF = rewriteF t.task_known in
  add_decl task (decl_map fnT fnF t.task_decl)

let comp = Register.store (fun () -> Trans.map comp None)

let () = Driver.register_transform "compile_match" comp

