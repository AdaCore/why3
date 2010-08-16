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

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let logic_to_logic lsymbol =
    if ls_equal lsymbol ps_equ then lsymbol else
    let new_ty = ls_ty_freevars lsymbol in
    (* as many t as type vars *)
    if Stv.is_empty new_ty then lsymbol (* same type *) else
      let add _ acc = my_t :: acc in
      let args = Stv.fold add new_ty lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      Term.create_lsymbol (id_clone lsymbol.ls_name) args lsymbol.ls_value

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
      let terms = args_transform tblT tblL varM f terms (Some t.t_ty) in
      t_app (findL tblL f) terms t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) t

  (** translation of formulae *)
  and fmla_transform tblT tblL varM f = match f.f_node with
      (* first case : predicate (not =), we must translate it and its args *)
    | Fapp(p,terms) when not (ls_equal p ps_equ) ->
      let terms = args_transform tblT tblL varM p terms None in
      f_app (findL tblL p) terms
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform tblT tblL varM) (fmla_transform tblT tblL varM) f

  and args_transform tblT tblL varM ls args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ls_app_inst ls args ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform tblT tblL varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = ty_to_term tblT varM ty :: acc in
    Mtv.fold add tv_to_ty args

  (** transforms a list of logic declarations into another.
  Declares new lsymbols with explicit polymorphic signatures.
  @param tblT binds type symbols to logic symbols
  @param tblL hashtable used to memoize new lsymbols *)
  let logic_transform tblT tblL decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL tblL lsymbol in (* new lsymbol *)
      let vars,expr = open_ls_defn ldef in
      let add v (vl,vm) =
        let vs = Term.create_vsymbol (id_fresh "t") my_t in
        vs :: vl, Mtv.add v vs vm
      in
      let vars,varM = Stv.fold add (ls_ty_freevars lsymbol) (vars,Mtv.empty) in
      (match expr with
      | Term t ->
          let t = term_transform tblT tblL varM t in
          Decl.make_fs_defn new_lsymbol vars t
      | Fmla f ->
          let f = fmla_transform tblT tblL varM f in
          Decl.make_ps_defn new_lsymbol vars f)
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
let () = 
  Encoding.register_enco_poly "explicit" (fun _ -> explicit_polymorphism)

