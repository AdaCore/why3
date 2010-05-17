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
open Ty
open Term
open Decl
open Task

(* TODO : preserve some types (builtin types) ? *)


let decl_transform tbl d = match d.d_node with
| Dtype tys -> failwith "Dtype : not implemented"
| Dind inds -> failwith "Dind : should not be here !"
| Dlogic decls -> failwith "not implemented"
| Dprop prop -> failwith "not implemented"


(** the transformation to be registered. *)
let explicit_polymorphism = Register.store
  (fun () -> Trans.decl (decl_transform (Hashtbl.create 42)) None)

let () = Register.register_transform "explicit_polymorphism" explicit_polymorphism

