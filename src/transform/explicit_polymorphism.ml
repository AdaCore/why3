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

(*s transformation from polymorphic logic to untyped logic. The polymorphic
logic must not have finite support types. *)

(* TODO : preserve builtin types *)

open Util
open Ident
open Ty
open Term
open Decl
open Task

(** type representing types *)
let t = Ty.create_tysymbol (id_fresh "t") [] None
let t_decl = Decl.create_ty_decl [(t, Tabstract)]

(*s module to separate utilities from important functions *)
module Prelude = struct

  (** [find construct tbl id] searches for the ident associated with [id] in [tbl].
  It creates it with [construct id] if it cannot find it. *)
  let find_ construct tbl id =
    try Hashtbl.find tbl id
    with Not_found ->
      let new_image = construct id in
      Hashtbl.add tbl id new_image;
      new_image

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let logic_to_logic _lsymbol = failwith "not implemented"

  let find = find_ logic_to_logic

  (** transforms a list of logic declarations into another *)
  let logic_transform tbl decls = List.map
  (function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = find tbl lsymbol in
      let polymorphic_vars = List.filter (* get polymorphic vars *)
        (fun ty -> match ty.ty_node with Tyvar _ -> true|_-> false)
        lsymbol.ls_args in
      let vars,expr = open_ls_defn ldef in
      let new_vars = List.map
        (fun _ -> Term.create_vsymbol (id_fresh "t") (ty_app t []))
        polymorphic_vars in
      let vars = List.append new_vars vars in (* add new vars *)
      Decl.make_ls_defn new_lsymbol vars expr
    | (lsymbol, None) ->
      let new_lsymbol = find tbl lsymbol in
      (new_lsymbol, None))
  decls


end

(** main function, takes a hashtable (for memoization) and a declaration
and returns the corresponding declaration in explicit polymorphism logic. *)
let decl_transform tbl d = match d.d_node with
| Dind _inds -> failwith "Dind : should not be here !"
| Dtype _tys -> failwith "Dtype : not implemented"
| Dlogic decls -> [Decl.create_logic_decl (Prelude.logic_transform tbl decls)]
| Dprop _prop -> failwith "Dprop : not implemented"


(** the transformation to be registered. *)
let explicit_polymorphism =
  let prelude_task = Task.add_decl None t_decl in (* declare t first *)
  Register.store
    (fun () -> Trans.decl (decl_transform (Hashtbl.create 42)) prelude_task)

let () = Register.register_transform
  "explicit_polymorphism"
  explicit_polymorphism

