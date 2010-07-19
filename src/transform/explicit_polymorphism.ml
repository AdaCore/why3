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

(**s transformation from polymorphic logic to untyped logic. The polymorphic
logic must not have finite support types. *)


open Util
open Ident
open Ty
open Term
open Decl
open Task


(** module with printing functions *)
module Debug = struct
  let print_mtv vprinter fmter m =
    Mtv.iter (fun key value -> Format.fprintf fmter "@[%a@] -> @[%a@]@."
      Pretty.print_tv key vprinter value) m

  let print_mty vprinter fmter m =
    Mty.iter (fun key value -> Format.fprintf fmter "@[%a@] -> @[%a@]@."
      Pretty.print_ty key vprinter value) m

  (** utility to print a list of items *)
  let rec print_list printer fmter = function
    | [] -> Format.fprintf fmter ""
    | e::es -> if es = []
        then Format.fprintf fmter "@[%a@] %a" printer e (print_list printer) es
        else Format.fprintf fmter "@[%a@], %a" printer e (print_list printer) es

  let debug x = Format.eprintf "%s@." x
end




(** {2 small functions} *)

module Utils = struct

  (** parenthesing operator *)
  let ($) f x = f x

  let const x _ = x

  let map_keys m = Mty.fold (fun key _ acc -> key::acc) m []
  let map_values m = Mty.fold (fun _ value acc -> value::acc) m []


  (** type representing types *)
  let t = Ty.create_tysymbol (id_fresh "ty") [] None
  let my_t = ty_app t []
  let t_decl = Decl.create_ty_decl [(t, Tabstract)]

  let has_type_t = ty_equal my_t

  let is_tyvar = function
    | Tyvar _ -> true | _ -> false
  let from_tyvar = function
    | Tyvar x -> x | _ -> failwith "from_tyvar called on non-tyvar"
  let isSome = function
    | Some _ -> true | _ -> false
  let fromSome = function
    | Some x -> x | None -> failwith "fromSome called on None"

  (** list from 1 to n *)
  let range n =
    let rec helper acc = function
      | 0 -> acc
      | n -> helper (n :: acc) (n-1)
    in helper [] n

  (** [drop n l] is [l], without its [n] first elements *)
  let rec drop n l = match (n,l) with
    | (0, _) -> l
    | (_, []) -> failwith "dropping items from empty list"
    | (_, _::xs) -> drop (n-1) xs

  (** explore a type to seek all type vars *)
  let rec find_tyvars tyvars ty = match ty.ty_node with
    | Tyvar _ -> (* test if ty has already been found *)
      (try ignore $ List.find
        (fun x -> x.ty_tag = ty.ty_tag) tyvars; tyvars
      with Not_found -> ty::tyvars)
    | Tyapp (_, tys) -> List.fold_left find_tyvars tyvars tys
  (** predicate to check whether a type has type vars *)
  and has_tyvars ty = match ty.ty_node with
    | Tyvar _ -> true
    | Tyapp (_, tys) -> List.exists has_tyvars tys

  (** returns all type vars (free) in given fmla [f] *)
  let rec f_find_type_vars acc f = match f.f_node with
    | Fapp (p, terms) ->
      let new_acc = if isSome p.ls_value
        then find_tyvars acc (fromSome p.ls_value) else acc in
      List.fold_left t_find_type_vars new_acc terms
    | _ -> f_fold t_find_type_vars f_find_type_vars acc f
  (** returns all type vars in given term *)
  and t_find_type_vars acc t =
    let acc = find_tyvars acc t.t_ty in
    match t.t_node with
    | Tvar x -> find_tyvars acc x.vs_ty
    | _ -> t_fold t_find_type_vars f_find_type_vars acc t
  (** returns all type vars in given lsymbol *)
  and l_find_type_vars l =
    let acc = match l.ls_value with
      | None -> []
      | Some ty -> find_tyvars [] ty in
    List.fold_left find_tyvars acc l.ls_args


  (** [find_matching_vars tv_to_ty left right] matches [left]
  against [right] to deduce a mapping from type vars in [left]
  to types in [right]. [tv_to_ty] is a mapping given in argument.
  It must be compliant with the unification between [left] and [right] *)
  let rec find_matching_vars tv_to_ty left right =
    (*Format.eprintf "matching @[%a@] with @[%a@]@."
      (Debug.print_list Pretty.print_ty) left
      (Debug.print_list Pretty.print_ty) right;*)
    assert (List.length left = List.length right);
    let tv_to_ty = List.fold_left2 ty_match tv_to_ty left right in
    (*Format.eprintf "gives @[%a@]@."
      (Debug.print_mtv Pretty.print_ty) tv_to_ty; flush stderr;*)
    tv_to_ty

  module Mint = Map.Make(
    struct
      type t = int
      let compare = Pervasives.compare
    end)

  (** [bind_nums_to_type_vars l] takes a lsymbol [l], and binds 1..n (where
  n is the number of type vars in [l]) to type vars of [l] *)
  let bind_nums_to_type_vars l =
    let type_vars = l_find_type_vars l in
    let n = List.length type_vars in
    List.fold_left2 (fun acc key value -> Mint.add key value acc)
      Mint.empty (range n) type_vars


end

let ts_ty = Utils.t

(* from now on, we shall use those functions without module qualification *)
open Utils

(** {2 module to separate utilities from important functions} *)

module Transform = struct

  (** {1 memoization facilities} *)

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
    let ty_vars = match lsymbol.ls_value with (* do not forget result type *)
      | Some t -> t::lsymbol.ls_args | None -> lsymbol.ls_args in
    let new_ty = (List.fold_left find_tyvars [] ty_vars) in
    (* as many t as type vars *)
    if new_ty = [] then lsymbol (* same type *) else
      let new_ty = List.map (const my_t) new_ty in
      let all_new_ty = new_ty @ lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      let new_lsymbol =
        Term.create_lsymbol (id_clone lsymbol.ls_name)
          all_new_ty lsymbol.ls_value in
      new_lsymbol

  (** creates a lsymbol associated with the given tysymbol *)
  let type_to_logic ty =
    let name = id_clone ty.ts_name in
    let args = (List.map (const my_t) ty.ts_args) in
    Term.create_lsymbol name args (Some my_t)


  (** different finders for logic and type declarations *)

  let findL tbl x = find_generic logic_to_logic tbl x
  let findT tbl x = find_generic type_to_logic tbl x

  (** {1 transformations} *)

  (** transforms a type into another *)
  let rec ty_to_ty tv_to_ty ty = match ty.ty_node with
    | Tyvar x -> (try Mtv.find x tv_to_ty with Not_found -> ty)
    | Tyapp(typ, tys) -> ty_app typ (List.map (ty_to_ty tv_to_ty) tys)

  (** transforms a type into a term (new args of polymorphic symbols).
      [tblT] is a hashtable used to associate types and symbols
      [varM] is a Map used to associate some type vars and symbols *)
  let rec ty_to_term tblT varM tv_to_ty ty =
    match ty.ty_node with
    | Tyvar _ ->
      let new_ty = ty_to_ty tv_to_ty ty in
      begin match new_ty.ty_node with
        | Tyvar _ -> (* var -> var, stop there *)
          assert (Mty.mem new_ty varM);
          t_var (Mty.find new_ty varM)
        | Tyapp _ -> (* recur *)
          ty_to_term tblT varM tv_to_ty new_ty
      end
    | Tyapp(typ, tys) ->
      assert (Hashtbl.mem tblT typ); (* nonsense otherwise *)
      let lsymbol = Hashtbl.find tblT typ in
      let terms = List.map (ty_to_term tblT varM tv_to_ty) tys in
      t_app lsymbol terms my_t



  (** translation of terms *)
  let rec term_transform tblT tblL varM t = match t.t_node with
    | Tapp(f, terms) ->
      let new_f = findL tblL f in
      (* first, remember an order for type vars of new_f *)
      let type_vars = l_find_type_vars new_f in
      (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
      let int_to_tyvars = bind_nums_to_type_vars new_f in
      (* match types *)
      let args_to_match = drop (List.length type_vars) new_f.ls_args in
      let concrete_ty = List.map (fun x-> x.t_ty) terms in
      let result_to_match = fromSome new_f.ls_value in
      let result_ty = t.t_ty in
      let tv_to_ty = find_matching_vars Mtv.empty
        (result_to_match :: args_to_match) (result_ty :: concrete_ty) in
      (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
      (* fresh terms to be added at the beginning of the list of arguments *)
      let new_ty_int = range (List.length type_vars) in
      let new_ty = List.map (fun x -> Mint.find x int_to_tyvars) new_ty_int in
      let new_terms = List.map (ty_to_term tblT varM tv_to_ty) new_ty in
      let transformed_terms = List.map
        (term_transform tblT tblL varM) terms in
      let transformed_result = ty_to_ty tv_to_ty (fromSome new_f.ls_value) in
      t_app new_f (new_terms @ transformed_terms) transformed_result
      | _ -> (* default case : traverse *)
        t_map (term_transform tblT tblL varM)
          (fmla_transform tblT tblL varM) t
  (** translation of formulae *)
  and fmla_transform tblT tblL varM f = match f.f_node with
      (* first case : predicate (not = or <>), we must translate it and its args *)
    | Fapp(p,terms) when (not (ls_equal p ps_equ)) && not(ls_equal p ps_neq) ->
      let new_p = findL tblL p in
      (* first, remember an order for type vars of new_f *)
      let type_vars = l_find_type_vars new_p in
      (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
      let int_to_tyvars = bind_nums_to_type_vars new_p in
      (* match types *)
      let args_to_match = drop (List.length type_vars) new_p.ls_args in
      let concrete_ty = List.map (fun x-> x.t_ty) terms in
      let tv_to_ty = find_matching_vars Mtv.empty
         args_to_match concrete_ty in
      (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
      (* fresh terms to be added at the beginning of the list of arguments *)
      let new_ty_int = range (List.length type_vars) in
      let new_ty = List.map (fun x -> Mint.find x int_to_tyvars) new_ty_int in
      let new_terms = List.map (ty_to_term tblT varM tv_to_ty) new_ty in
      let transformed_terms = List.map
        (term_transform tblT tblL varM) terms in
      f_app new_p (new_terms @ transformed_terms)
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform tblT tblL varM)
        (fmla_transform tblT tblL varM) f



  (** transforms a list of logic declarations into another.
  Declares new lsymbols with explicit polymorphic signatures.
  @param tbl hashtable used to memoize new lsymbols *)
  let logic_transform tbl decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL tbl lsymbol in (* new lsymbol *)
      let polymorphic_vars = List.fold_left find_tyvars []
          lsymbol.ls_args in (* get unique type vars *)
      let vars,expr = open_ls_defn ldef in
      let new_vars = List.map
        (fun _ -> Term.create_vsymbol (id_fresh "t") my_t)
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
      | (ty_symbol, Tabstract) -> (findT tbl ty_symbol, None)
      | _ -> failwith "type_transform : no algebraic type should remain !" in
    let cur_decl = List.map helper tys in
    [Decl.create_ty_decl tys; Decl.create_logic_decl cur_decl]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform tblT tblL (prop_kind, prop_name, fmla) =
    let type_vars = (f_find_type_vars [] fmla) in
    let varM = List.fold_left (* create a vsymbol for each type var *)
      (fun m x -> Mty.add x (create_vsymbol (id_fresh "v") my_t) m)
      Mty.empty type_vars in
    (* Debug.print_mty Pretty.print_vs Format.err_formatter varM;
    Format.eprintf "-----------@."; *)
    (*universal quantification over ty vars*)
    let new_fmla = (fmla_transform tblT tblL varM fmla) in
    let quantified_fmla = f_forall (map_values varM) [] new_fmla in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

(** main function, takes hashtables (for memoization of types and logic
    symbols) and a declaration, and returns the corresponding declaration in
    explicit polymorphism logic.
    It is to be applied on every declarations of the task. *)
let decl_transform tblT tblL d =
  (*Format.eprintf "%a@." Pretty.print_decl d;*)
  let result = match d.d_node with
    | Dind _inds ->
    failwith "Dind : should not have inductives declarations at this point !"
    | Dtype tys -> Transform.type_transform tblT tys
    | Dlogic decls -> Transform.logic_transform tblL decls
    | Dprop prop -> Transform.prop_transform tblT tblL prop in
  (*Format.eprintf "===@.%a@.@." (Debug.print_list Pretty.print_decl) result;*)
  result


(** the transformation to be registered.
    It creates two new hashtables, used everywhere, which updates are
    shared by side effects. *)
let explicit_polymorphism =
  let prelude_task = Task.add_decl None t_decl in (* declare t first *)
  Trans.decl
      (decl_transform (Hashtbl.create 21) (Hashtbl.create 42)) prelude_task


let () = Trans.register_transform "explicit_polymorphism" explicit_polymorphism

