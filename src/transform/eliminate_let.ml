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

let rec rewriteT t = match t.t_node with
  | Tlet (t,tb) ->
      let v,e = t_open_bound tb in
      rewriteT (t_subst_single v t e)
  | _ -> t_map rewriteT rewriteF t

and rewriteF f = match f.f_node with
  | Flet (t,fb) ->
      let v,e = f_open_bound fb in
      rewriteF (f_subst_single v t e)
  | _ -> f_map rewriteT rewriteF f

let comp = Register.store (fun () -> Trans.rewrite rewriteT rewriteF None)

let () = Driver.register_transform "eliminate_let" comp

