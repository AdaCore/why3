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

open Theory

let elt a =
  let rec aux first_level acc d = match first_level, d.d_node with
    | _,Duse t -> Context.ctxt_fold (aux false) acc t.th_ctxt
    | false,Dprop (Pgoal,_) -> acc
    | false,Dprop (Plemma,pr) -> create_prop_decl Paxiom pr::acc
    | _ -> d::acc 
  in
  let r =  (aux true [] a) in
  (*Format.printf "flat %a : %a@\n" Pretty.print_decl a Pretty.print_decl_list r;*)
  r


let t = Transform.elt elt
