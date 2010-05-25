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




(** {2 small functions} *)

module Utils = struct

  (** parenthesing operator *)
  let ($) f x = f x

  (** type representing types *)
  let t = Ty.create_tysymbol (id_fresh "t") [] None
  let t_decl = Decl.create_ty_decl [(t, Tabstract)]

  let has_type_t = ty_equal (ty_app t [])

  let is_tyvar = function
    | Tyvar _ -> true | _ -> false
  and from_tyvar = function
    | Tyvar x -> x | _ -> failwith "from_tyvar called on non-tyvar"
  let fromSome = function
    | Some x -> x | None -> failwith "fromSome called on None"

  (** returns all type vars (free) in given fmla_node *)
  let rec find_type_vars acc f = match f.f_node with
    | Fapp (p, terms) ->
      let new_acc = List.filter
        (fun x -> is_tyvar x.ty_node) p.ls_args in
      List.fold_left term_analyse (new_acc @ acc) terms
    | _ -> f_fold term_analyse find_type_vars acc f
  and term_analyse acc t = match t.t_node with
    | Tvar x when is_tyvar (x.vs_ty.ty_node) -> x.vs_ty::acc
    | _ -> t_fold term_analyse find_type_vars acc t


  (** kind of composition of filter and map *)
  let rec mapSome f = function
    | e::es -> (match f e with
      | Some x -> x :: mapSome f es
      | None -> mapSome f es)
    | [] -> []

  let from_ty_node = function
    | Tyvar _ -> assert false
    | Tyapp (ty_symb, vars) -> (ty_symb, vars)

  (** to get unique elements in list (inefficient) *)
  let list_unique l =
    let remember memory x = if List.mem x memory
      then memory else x::memory in
    List.fold_left remember [] l (* FIXME : make it efficient *)

  let const x _ = x

  let map_keys m = Mty.fold (fun key _value acc -> key::acc) m []
  let map_values m = Mty.fold (fun _key value acc -> value::acc) m []

end

open Utils


(** {2 module to separate utilities from important functions} *)

module Prelude = struct

  (** [find construct tbl id] searches for the object associated with
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
    if ls_equal lsymbol ps_equ || ls_equal lsymbol ps_neq then lsymbol else
    let new_ty = list_unique $
      List.filter (fun x->is_tyvar x.ty_node) lsymbol.ls_args in
    (* as many t as type vars *)
    if new_ty = [] then lsymbol (* same type *) else
      let new_ty = List.map (fun _ -> ty_app t []) new_ty in
      let all_new_ty = new_ty @ lsymbol.ls_args in
      let new_lsymbol =
	Term.create_lsymbol (id_clone lsymbol.ls_name)
	  all_new_ty lsymbol.ls_value
      in new_lsymbol

  (** creates a lsymbol associated with the given type *)
  let type_to_logic ty =
    let my_t = ty_app t [] in
    let name = id_clone ty.ts_name in
    let args = (List.map (fun _-> my_t) ty.ts_args) in
    let new_lsymbol =
      Term.create_lsymbol name args (Some my_t)
    in new_lsymbol
  
  (** [find_matching_vars tblT varM args_ty args_vars] matches [args_ty]
  against [args_vars] to deduce a mapping from [args_vars] to lsymbols
  through [tblT] and [varM] *)
  let find_matching_vars _tblT varM args_ty args_vars =
    let tv_to_ty = Mtv.empty in
    let mapping = List.fold_left2 ty_match tv_to_ty args_ty args_vars in
    let tv_to_lsymbol = Mtv.empty in (* result mapping *)
    Mtv.fold
      (fun key value acc -> Mtv.add key (Mty.find value varM) acc)
      mapping tv_to_lsymbol 


  (** different finders *)

  let findL tbl x = find_generic logic_to_logic tbl x
  let findT tbl x = find_generic type_to_logic tbl x

  (** substitutions in formulae and terms *)
  let rec term_transform tblT tblL varM t = match t.t_node with
    | Tapp(f, terms) ->
      let result_ty = fromSome f.ls_value in
      let new_f = (findL tblL f) in
      let args_ty = List.map (fun x-> x.t_ty) terms in
      let matched_terms = find_matching_vars tblT varM args_ty new_f.ls_args in
      let new_terms = List.filter (fun x->is_tyvar x.ty_node) f.ls_args in
      let new_terms = List.map 
        (fun x-> match x.ty_node with 
          | Tyvar v -> t_var (Mtv.find v matched_terms)
          | _ -> failwith "should find a mapping for this var") new_terms in
      let transformed_terms = List.map (term_transform tblT tblL varM) terms in
      t_app new_f (new_terms @ transformed_terms) result_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) t
  and fmla_transform tblT tblL varM f = f_map
    (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) f


  (** transforms a list of logic declarations into another
  @param tbl hashtable used to memoize new lsymbols *)
  let logic_transform tbl decls =
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL tbl lsymbol in (* new lsymbol *)
      let polymorphic_vars = list_unique $ List.filter
        (fun ty -> match ty.ty_node with Tyvar _ -> true|_-> false)
        lsymbol.ls_args in (* get unique type vars *)
      let vars,expr = open_ls_defn ldef in
      let new_vars = List.map
        (fun _ -> Term.create_vsymbol (id_fresh "t") (ty_app t []))
        polymorphic_vars in (* new vars for polymorphism *)
      let vars = List.append new_vars vars in (* add new vars in signature *)
      (match expr with
      | Term t -> Decl.make_fs_defn new_lsymbol vars t
      | Fmla f -> Decl.make_ps_defn new_lsymbol vars (f_forall new_vars [] f))
    | (lsymbol, None) ->
      let new_lsymbol = findL tbl lsymbol in
      (new_lsymbol, None) in
    let cur_decl = List.map helper decls
    in [Decl.create_logic_decl cur_decl]


  (** transforms a list of type declarations *)
  let type_transform tbl tys =
    let helper = function
    | (ty_symbol, Tabstract) ->
      let new_lsymbol = findT tbl ty_symbol in
      (new_lsymbol, None)
    | _ -> failwith "type_transform : no algebraic type should remain !" in
    let cur_decl = List.map helper tys
    in [Decl.create_ty_decl tys; Decl.create_logic_decl cur_decl]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform tblT tblL (prop_kind, prop_name, fmla) =
    let type_vars = list_unique $ find_type_vars [] fmla in
    let varM = List.fold_left
      (fun m x -> Mty.add x
          (create_vsymbol (id_fresh "t") (ty_app t [])) m)
      Mty.empty type_vars
    in [Decl.create_prop_decl prop_kind prop_name
       (f_forall (map_values varM) [] (*universal quantification over ty vars*)
          (fmla_transform tblT tblL varM fmla))]

end

(** {2 main part} *)

(** utility to print a list of items *)
let rec print_list printer fmter = function
  | [] -> ()
  | e::es ->
    Format.fprintf fmter "%a,@ %a" printer e (print_list printer) es

(** main function, takes hashtables (for memoization of types and logic
symbols) and a declaration, and returns the corresponding declaration in
explicit polymorphism logic. *)
let decl_transform tblT tblL d =
  (* Format.eprintf "%a@ " Pretty.print_decl d; *)
  let result = match d.d_node with
    | Dind _inds ->
    failwith "Dind : should not have inductives declarations at this point !"
    | Dtype tys -> Prelude.type_transform tblT tys
    | Dlogic decls -> Prelude.logic_transform tblL decls
    | Dprop prop -> Prelude.prop_transform tblT tblL prop
  in (* Format.eprintf " ===> %a@." (print_list Pretty.print_decl) result; *)
  result

(** the transformation to be registered. *)
let explicit_polymorphism =
  let prelude_task = Task.add_decl None t_decl in (* declare t first *)
  Register.store
    (fun () -> Trans.decl
      (decl_transform (Hashtbl.create 42) (Hashtbl.create 42)) prelude_task)

let () = Register.register_transform
  "explicit_polymorphism"
  explicit_polymorphism

