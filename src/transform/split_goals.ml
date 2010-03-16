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
open Ident
open Theory  
open Context

let t ?filter () =
  let filter = match filter with
    | None -> (fun _ -> true)
    | Some s -> (fun id -> Sid.mem id s) in
  let f ctxt0 ((ctxt,l) as ctxtl) =
    let decl = ctxt0.ctxt_decl in
    match decl.d_node with
      | Dprop (Pgoal, pr, _) when filter (pr_name pr) -> (ctxt, add_decl ctxt decl :: l)
      | Dprop (Pgoal, pr, _)  -> ctxtl
      | Dprop (Plemma, pr, f) when filter (pr_name pr) ->
          let d1 = create_prop_decl Paxiom pr f in
          let d2 = create_prop_decl Pgoal  pr f in
          (add_decl ctxt d1,
           add_decl ctxt d2 :: l)
      | Dprop (Plemma, pr, f) ->
          let d1 = create_prop_decl Paxiom pr f in
          (add_decl ctxt d1,l)
      | _ -> (add_decl ctxt decl, l) 
  in
  let g = Transform.fold f (fun env -> init_context env, []) in
  Transform.conv_res g snd
