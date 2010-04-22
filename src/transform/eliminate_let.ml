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

let rec rewrite_t map t =
  match t.t_node with
    | Tlet (t1,tb) ->
        let t1 = rewrite_t map t1 in
        let vs,t2 = t_open_bound tb in
        rewrite_t (Mvs.add vs t1 map) t2
    | Tvar vs ->
        begin try
          Mvs.find vs map
        with Not_found -> t end
    | _ -> t_map (rewrite_t map) (rewrite_f map) t

and rewrite_f map f =
  match f.f_node with
    | Flet (t1,fb) ->
        let t1 = rewrite_t map t1 in
        let vs,f2 = f_open_bound fb in
        rewrite_f (Mvs.add vs t1 map) f2
    | _ -> f_map (rewrite_t map) (rewrite_f map) f

let remove_let_t = rewrite_t Mvs.empty
let remove_let_f = rewrite_f Mvs.empty

let eliminate_let =
  Register.store (fun () -> Trans.rewrite remove_let_t remove_let_f None)

let () = Register.register_transform "eliminate_let" eliminate_let

