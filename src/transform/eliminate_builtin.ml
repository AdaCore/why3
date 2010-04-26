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

open Util
open Ident
open Term
open Decl

let add_ld q = function
  | ls, Some _ when Driver.query_remove q ls.ls_name -> (ls, None)
  | d -> d

let add_id q (ld,id) = function
  | ls, _ when Driver.query_remove q ls.ls_name -> (ls, None)::ld, id
  | d -> ld, d::id

let elim q d = match d.d_node with
  | Dlogic l ->
      create_logic_decls (List.map (add_ld q) l)
  | Dind l ->
      let ld, id = List.fold_left (add_id q) ([],[]) l in
      create_logic_decls (List.rev ld) @ create_ind_decls (List.rev id)
  | _ -> [d]

let eliminate_builtin =
  Register.store_query (fun q -> Trans.decl (elim q) None)

let () = Register.register_transform "eliminate_builtin" eliminate_builtin

