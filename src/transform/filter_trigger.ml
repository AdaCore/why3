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

let make_rt_rf keep =
  let rec rt t = t_map rt rf t
  and rf f = 
    let f = f_map rt rf f in
    match f.f_node with
      | Fquant (Fforall,fq) ->
        let vsl,trl,f2 = f_open_quant fq in
        let one_false = ref false in
        let keep x = let b = keep x in
                     if b then b else (one_false := true; b) in
        let trl = List.filter (List.for_all keep) trl in
        if not (!one_false) then f else f_forall vsl trl f2
      | _ -> f in
  rt,rf


let keep_no_predicate = function
        | Term _ -> true
        | _ -> false

  
let filter_trigger_no_predicate = 
  Register.store (fun () -> 
    let rt,rf = make_rt_rf keep_no_predicate in
    Trans.rewrite rt rf None)

let () = Register.register_transform "filter_trigger_no_predicate" 
  filter_trigger_no_predicate


let keep_no_fmla = function
        | Term _ -> true
        | Fmla {f_node = Fapp (ps,_)} -> not (ls_equal ps ps_equ)
        | _ -> false


let filter_trigger = Register.store 
  (fun () -> 
    let rt,rf = make_rt_rf keep_no_fmla in
    Trans.rewrite rt rf None)

let () = Register.register_transform "filter_trigger" filter_trigger


let keep_no_builtin query = function
        | Term _ -> true
        | Fmla {f_node = Fapp (ps,_)} ->
          Driver.query_syntax query ps.ls_name = None
        | _ -> false

  
let filter_trigger_builtin = 
  Register.store_query (fun query -> 
    let rt,rf = make_rt_rf (keep_no_builtin query) in
    Trans.rewrite rt rf None)

let () = Register.register_transform "filter_trigger_builtin" 
  filter_trigger_builtin
