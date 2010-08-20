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
open Libencoding

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

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let findL = Wls.memoize 63 (fun lsymbol ->
    if ls_equal lsymbol ps_equ then lsymbol else
    let new_ty = ls_ty_freevars lsymbol in
    (* as many t as type vars *)
    if Stv.is_empty new_ty then lsymbol (* same type *) else
      let add _ acc = ty_type :: acc in
      let args = Stv.fold add new_ty lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      Term.create_lsymbol (id_clone lsymbol.ls_name) args lsymbol.ls_value)

  (** {1 transformations} *)

  (** translation of terms *)
  let rec term_transform varM t = match t.t_node with
    | Tapp(f, terms) ->
      let terms = args_transform varM f terms (Some t.t_ty) in
      t_app (findL f) terms t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform varM) (fmla_transform varM) t

  (** translation of formulae *)
  and fmla_transform varM f = match f.f_node with
      (* first case : predicate (not =), we must translate it and its args *)
    | Fapp(p,terms) when not (ls_equal p ps_equ) ->
      let terms = args_transform varM p terms None in
      f_app (findL p) terms
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform varM) (fmla_transform varM) f

  and args_transform varM ls args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ls_app_inst ls args ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = term_of_ty varM ty :: acc in
    Mtv.fold add tv_to_ty args

  (** transforms a list of logic declarations into another.
  Declares new lsymbols with explicit polymorphic signatures. *)
  let logic_transform decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL lsymbol in (* new lsymbol *)
      let vars,expr = open_ls_defn ldef in
      let add v (vl,vm) =
        let vs = Term.create_vsymbol (id_fresh "t") ty_type in
        vs :: vl, Mtv.add v vs vm
      in
      let vars,varM = Stv.fold add (ls_ty_freevars lsymbol) (vars,Mtv.empty) in
      (match expr with
      | Term t ->
          let t = term_transform varM t in
          Decl.make_fs_defn new_lsymbol vars t
      | Fmla f ->
          let f = fmla_transform varM f in
          Decl.make_ps_defn new_lsymbol vars f)
    | (lsymbol, None) ->
      (findL lsymbol, None)
    in
    [Decl.create_logic_decl (List.map helper decls)]

  (** transforms a closed formula *)
  let sentence_transform fmla =
    let type_vars = f_ty_freevars Stv.empty fmla in
    let varM = Stv.fold (* create a vsymbol for each type var *)
      (fun x m -> Mtv.add x (create_vsymbol (id_fresh "t") ty_type) m)
      type_vars Mtv.empty in
    (* Debug.print_mtv Pretty.print_vs Format.err_formatter varM;
    Format.eprintf "-----------@."; *)
    (*universal quantification over ty vars*)
    let new_fmla = fmla_transform varM fmla in
    let vars = Mtv.fold (fun _ value acc -> value::acc) varM [] in
    f_forall_close vars [] new_fmla

  (** transform an inductive declaration *)
  let ind_transform idl =
    let iconv (pr,f) = pr, sentence_transform f in
    let conv (ls,il) = findL ls, List.map iconv il in
    [Decl.create_ind_decl (List.map conv idl)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform (prop_kind, prop_name, fmla) =
    let quantified_fmla = sentence_transform fmla in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

let decl d = match d.d_node with
  | Dtype tdl -> d :: Libencoding.lsdecl_of_tydecl tdl
  | Dlogic ldl -> Transform.logic_transform ldl
  | Dind idl -> Transform.ind_transform idl
  | Dprop prop -> Transform.prop_transform prop

let explicit = Trans.decl decl (Task.add_decl None d_ts_type)

(** {2 monomorphise task } *)

let lsmap kept = Wls.memoize 63 (fun ls ->
  let tymap ty =
    if Sty.mem ty kept then ty else Libencoding.ty_base in
  let ty_res = Util.option_map tymap ls.ls_value in
  let ty_arg = List.map tymap ls.ls_args in
  if Util.option_eq ty_equal ty_res ls.ls_value &&
     List.for_all2 ty_equal ty_arg ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res)

let monomorph = Trans.on_meta Encoding.meta_kept (fun tds ->
  let kept = Libencoding.get_kept_types tds in
  let decl = Libencoding.d_monomorph kept (lsmap kept) in
  Trans.decl decl (Task.add_decl None d_ts_base))

let () = Encoding.register_enco_poly "explicit"
    (fun _ -> Trans.compose explicit monomorph)

