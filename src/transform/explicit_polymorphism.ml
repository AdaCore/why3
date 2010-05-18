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

  (** [find construct tbl id] searches for the ident associated with
  [id] in [tbl]. It creates it with [construct id] if it cannot find it. *)
  let find_generic construct tbl id =
    try Hashtbl.find tbl id
    with Not_found ->
      let new_image = construct id in
      Hashtbl.add tbl id new_image;
      new_image

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let logic_to_logic lsymbol =
    let replace ty = match ty.ty_node with
      | Tyvar _ -> ty_app t []
      | _ -> ty in
    let new_ty = List.map replace lsymbol.ls_args in
    Term.create_lsymbol
      (id_clone lsymbol.ls_name)
      new_ty
      lsymbol.ls_value

  (** creates a lsymbol associated with the given type *)
  let type_to_logic ty =
    let my_t = ty_app t [] in
    let name = "t" in
    let args = (List.map (fun _-> my_t) ty.ts_args) in
    let lsymbol = Term.create_lsymbol
      (id_fresh name) args (Some my_t) in
    (lsymbol, None)

  (** different finders *)

  let findL = find_generic logic_to_logic
  let findT = find_generic type_to_logic

  (** transforms a list of logic declarations into another
  @param tbl hashtable used to memoize new lsymbols *)
  let logic_transform tbl decls =
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL tbl lsymbol in (* new lsymbol *)
      let polymorphic_vars = List.filter
        (fun ty -> match ty.ty_node with Tyvar _ -> true|_-> false)
        lsymbol.ls_args in (* get polymorphic vars *)
      let vars,expr = open_ls_defn ldef in
      let new_vars = List.map
        (fun _ -> Term.create_vsymbol (id_fresh "t") (ty_app t []))
        polymorphic_vars in (* new vars for polymorphism *)
      let vars = List.append new_vars vars in (* add new vars in signature *)
      (match expr with
      | Term t -> Decl.make_fs_defn new_lsymbol vars t
      | Fmla f -> Decl.make_ps_defn new_lsymbol vars (f_forall new_vars [] f))
      (* FIXME : is it useful / meaningful ? *)
    | (lsymbol, None) ->
      let new_lsymbol = findL tbl lsymbol in
      (new_lsymbol, None)
    in [Decl.create_logic_decl (List.map helper decls)]


  (** transforms a list of type declarations *)
  let type_transform tbl tys =
    let helper = function
    | (ty_symbol, Tabstract) -> findT tbl ty_symbol
    | _ -> failwith "type_transform : no algebraic type should remain !"
    in [Decl.create_logic_decl (List.map helper tys)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform _tblT _tblL fmla =
    failwith "prop_transform : not implemented"

end

(** main function, takes hashtables (for memoization of types and logic
symbols) and a declaration, and returns the corresponding declaration in
explicit polymorphism logic. *)
let decl_transform tblT tblL d = match d.d_node with
| Dind _inds -> failwith "Dind : should not be here !"
| Dtype tys -> Prelude.type_transform tblT tys
| Dlogic decls -> Prelude.logic_transform tblL decls
| Dprop (prop_kind, prop_name, fmla) ->
  [Decl.create_prop_decl prop_kind prop_name
    (Prelude.prop_transform tblT tblL fmla)]


(** the transformation to be registered. *)
let explicit_polymorphism =
  let prelude_task = Task.add_decl None t_decl in (* declare t first *)
  Register.store
    (fun () -> Trans.decl
      (decl_transform (Hashtbl.create 42) (Hashtbl.create 42)) prelude_task)

let () = Register.register_transform
  "explicit_polymorphism"
  explicit_polymorphism

