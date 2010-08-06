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

(** type representing types *)
let ts_ty = Ty.create_tysymbol (id_fresh "ty") [] None
let my_t = ty_app ts_ty []
let t_decl = Decl.create_ty_decl [ts_ty, Tabstract]

(** module with printing functions *)
module Debug = struct
  let print_mtv vprinter fmter m =
    Mtv.iter (fun key value -> Format.fprintf fmter "@[%a@] -> @[%a@]@."
      Pretty.print_tv key vprinter value) m

  (** utility to print a list of items *)
  let rec print_list printer fmter = function
    | [] -> Format.fprintf fmter ""
    | e::es -> if es = []
        then Format.fprintf fmter "@[%a@] %a" printer e (print_list printer) es
        else Format.fprintf fmter "@[%a@], %a" printer e (print_list printer) es

  let debug x = Format.eprintf "%s@." x
end

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

  (** returns all type vars in given lsymbol *)
  let l_find_type_vars l =
    let acc = match l.ls_value with
      | None -> Stv.empty
      | Some ty -> ty_freevars Stv.empty ty in
    let s = List.fold_left ty_freevars acc l.ls_args in
    Stv.elements s

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let logic_to_logic lsymbol =
    if ls_equal lsymbol ps_equ || ls_equal lsymbol ps_neq then lsymbol else
    let new_ty = l_find_type_vars lsymbol in
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
    Term.create_fsymbol name args my_t

  (** different finders for logic and type declarations *)

  let findL tbl x = find_generic logic_to_logic tbl x
  let findT tbl x = find_generic type_to_logic tbl x

  (** {1 transformations} *)

  (** transforms a type into a term (new args of polymorphic symbols).
      [tblT] is a hashtable used to associate types and symbols
      [varM] is a Map used to associate some type vars and symbols *)
  let rec ty_to_term tblT varM ty = match ty.ty_node with
    | Tyvar v ->
      assert (Mtv.mem v varM);
      t_var (Mtv.find v varM)
    | Tyapp(typ, tys) ->
      assert (Hashtbl.mem tblT typ); (* nonsense otherwise *)
      let lsymbol = Hashtbl.find tblT typ in
      let terms = List.map (ty_to_term tblT varM) tys in
      t_app lsymbol terms my_t

  (** translation of terms *)
  let rec term_transform tblT tblL varM t = match t.t_node with
    | Tapp(f, terms) ->
      let new_f = findL tblL f in
      (* first, remember an order for type vars of new_f *)
      let type_vars = l_find_type_vars f in
      (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
      let tv_to_ty = t_app_inst f terms t.t_ty in
      (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
      (* fresh terms to be added at the beginning of the list of arguments *)
      let find_ty v = ty_to_term tblT varM (Mtv.find v tv_to_ty) in
      let new_terms = List.map find_ty type_vars in
      let transformed_terms = List.map (term_transform tblT tblL varM) terms in
      t_app new_f (new_terms @ transformed_terms) t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) t

  (** translation of formulae *)
  and fmla_transform tblT tblL varM f = match f.f_node with
      (* first case : predicate (not = or <>), we must translate it and its args *)
    | Fapp(p,terms) when (not (ls_equal p ps_equ)) && not(ls_equal p ps_neq) ->
      let new_p = findL tblL p in
      (* first, remember an order for type vars of new_f *)
      let type_vars = l_find_type_vars p in
      (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
      let tv_to_ty = f_app_inst p terms in
      (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
      (* fresh terms to be added at the beginning of the list of arguments *)
      let find_ty v = ty_to_term tblT varM (Mtv.find v tv_to_ty) in
      let new_terms = List.map find_ty type_vars in
      let transformed_terms = List.map (term_transform tblT tblL varM) terms in
      f_app new_p (new_terms @ transformed_terms)
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) f

  (** transforms a list of logic declarations into another.
  Declares new lsymbols with explicit polymorphic signatures.
  @param tblT binds type symbols to logic symbols
  @param tblL hashtable used to memoize new lsymbols *)
  let logic_transform tblT tblL decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL tblL lsymbol in (* new lsymbol *)
      let polymorphic_vars = l_find_type_vars lsymbol in
      let new_vars = List.map
        (fun _ -> Term.create_vsymbol (id_fresh "t") my_t)
        polymorphic_vars in (* new vars for polymorphism *)
      let varM = List.fold_left2 (fun m x v -> Mtv.add x v m)
        Mtv.empty polymorphic_vars new_vars in
      let vars,expr = open_ls_defn ldef in
      (match expr with
      | Term t ->
          let t = term_transform tblT tblL varM t in
          Decl.make_fs_defn new_lsymbol (new_vars @ vars) t
      | Fmla f ->
          let f = fmla_transform tblT tblL varM f in
          Decl.make_ps_defn new_lsymbol (new_vars @ vars) f)
    | (lsymbol, None) ->
      let new_lsymbol = findL tblL lsymbol in
      (new_lsymbol, None) in
    let cur_decl = List.map helper decls
    in [Decl.create_logic_decl cur_decl]

  (** transforms a list of type declarations *)
  let type_transform tblT tys =
    let helper acc = function
      | (ty_symbol, _) when ty_symbol.ts_def <> None -> acc
      | (ty_symbol, Tabstract) -> (findT tblT ty_symbol, None) :: acc
      | _ -> failwith "type_transform : no algebraic type should remain !" in
    let cur_decl = List.fold_left helper [] tys in
    Decl.create_ty_decl tys :: Decl.create_logic_decls cur_decl

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform tblT tblL (prop_kind, prop_name, fmla) =
    let type_vars = f_ty_freevars Stv.empty fmla in
    let varM = Stv.fold (* create a vsymbol for each type var *)
      (fun x m -> Mtv.add x (create_vsymbol (id_fresh "t") my_t) m)
      type_vars Mtv.empty in
    (* Debug.print_mtv Pretty.print_vs Format.err_formatter varM;
    Format.eprintf "-----------@."; *)
    (*universal quantification over ty vars*)
    let new_fmla = (fmla_transform tblT tblL varM fmla) in
    let vars = Mtv.fold (fun _ value acc -> value::acc) varM [] in
    let quantified_fmla = f_forall_close vars [] new_fmla in
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
    | Dind _ ->
      failwith "Dind : should not have inductive declarations at this point!"
    | Dtype tys -> Transform.type_transform tblT tys
    | Dlogic decls -> Transform.logic_transform tblT tblL decls
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

