(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** transformation from polymorphic logic to untyped logic. The polymorphic
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
        else Format.fprintf fmter "@[%a@], %a" printer e
        (print_list printer) es

  let debug x = Format.eprintf "%s@." x
end

(** {2 module to separate utilities from important functions} *)

module Transform = struct

    (* really return the map that replace all the variable of ty1,
       If the same variable appear in ty1 and ty2 Ty.ty_match doesn't
       bind this variable
    *)
  let rec ty_match2 s ty1 ty2 =
    match ty1.ty_node, ty2.ty_node with
      | Tyvar n1, _ ->
        Mtv.change n1 (function
          | None -> Some ty2
          | Some ty1 as r when ty_equal ty1 ty2 -> r
          | _ -> assert false) s
      | Tyapp (f1, l1), Tyapp (f2, l2) when ts_equal f1 f2 ->
        List.fold_left2 ty_match2 s l1 l2
      | _ -> assert false

  let fs_type =
    let alpha = ty_var (create_tvsymbol (id_fresh "a")) in
    create_fsymbol (id_fresh "type_of") [alpha] ty_type

  let app_type t = t_app fs_type [t] ty_type

  let type_variable_only_in_value lsymbol =
    let tvar_val = ty_freevars Stv.empty (of_option lsymbol.ls_value) in
    let tvar_arg = List.fold_left ty_freevars Stv.empty lsymbol.ls_args in
    Stv.diff tvar_val tvar_arg

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let findL = Wls.memoize 63 (fun lsymbol ->
    if ls_equal lsymbol ps_equ || lsymbol.ls_value = None then lsymbol else
    let new_ty = type_variable_only_in_value lsymbol in
    (* as many t as type vars *)
    if Stv.is_empty new_ty then lsymbol (* same type *) else
      let add _ acc = ty_type :: acc in
      let args = Stv.fold add new_ty lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      Term.create_lsymbol (id_clone lsymbol.ls_name) args lsymbol.ls_value)

  (** {1 transformations} *)

  (** translation of terms *)
  let rec term_transform kept varM t =
    match t.t_node with
    | Tapp(f, terms) ->
      let terms = args_transform kept varM f terms t.t_ty in
      t_app (findL f) terms t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform kept varM) (fmla_transform kept varM) t

  (** translation of formulae *)
  and fmla_transform kept varM f =
    match f.f_node with
      (* first case : predicate are not translated *)
    | Fapp(p,terms) ->
      let terms = List.map (term_transform kept varM) terms in
      f_app (findL p) terms
    | Fquant(q,b) ->
      let vsl,trl,fmla,cb = f_open_quant_cb b in
        (* TODO : how to modify the triggers? *)
      let guard fmla vs =
        if Sty.mem vs.vs_ty kept then fmla else
          let g = f_equ (app_type (t_var vs)) (term_of_ty varM vs.vs_ty) in
          f_implies g fmla in
      let fmla2 = List.fold_left guard (fmla_transform kept varM fmla) vsl in
      let trl = tr_map (term_transform kept varM)
        (fmla_transform kept varM) trl in
      f_quant q (cb vsl trl fmla2)
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform kept varM) (fmla_transform kept varM) f(*  in *)
    (* Format.eprintf "fmla_to : %a@." Pretty.print_fmla f;f *)

  and args_transform kept varM lsymbol args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ty_match2 Mtv.empty (of_option lsymbol.ls_value) ty in
    let new_ty = type_variable_only_in_value lsymbol in
    let tv_to_ty = Mtv.inter (fun _ tv () -> Some tv) tv_to_ty new_ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform kept varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = term_of_ty varM ty :: acc in
    Mtv.fold add tv_to_ty args

  let logic_guard kept acc lsymbol =
    match lsymbol.ls_value with
      | None -> acc
      | Some ty_val when Sty.mem ty_val kept -> acc
      | Some ty_val ->
        let varl = List.map (fun v -> create_vsymbol (id_fresh "x") v)
          lsymbol.ls_args in
        let stv = ls_ty_freevars lsymbol in
        let trans varM () =
          let terms = List.map t_var varl in
          let terms = args_transform kept varM lsymbol terms ty_val in
          let fmla =
            f_equ (app_type (t_app (findL lsymbol) terms ty_val))
              (term_of_ty varM ty_val) in
          let guard fmla vs =
            if Sty.mem vs.vs_ty kept then fmla else
              let g = f_equ (app_type (t_var vs)) (term_of_ty varM vs.vs_ty) in
              f_implies g fmla in
          let fmla = List.fold_left guard fmla varl in
          f_forall_close_simp varl [] fmla
        in
        let fmla = Libencoding.type_close stv trans () in
        Decl.create_prop_decl Paxiom
          (create_prsymbol (id_clone lsymbol.ls_name)) fmla::acc

  (** transforms a list of logic declarations into another.
      Declares new lsymbols with explicit polymorphic signatures,
      with guards only the type that appear in the return value type.
      *)
  let logic_transform kept decls =
    (* if there is a definition, we must take it into account *)
    let helper = function
    | (lsymbol, Some ldef) ->
      let new_lsymbol = findL lsymbol in (* new lsymbol *)
      let vars,expr = open_ls_defn ldef in
      let add v (vl,vm) =
        let vs = Term.create_vsymbol (id_fresh "t") ty_type in
        vs :: vl, Mtv.add v vs vm
      in
      let vars,varM =
        match lsymbol.ls_value with
          | None -> vars,Mtv.empty
          | Some ty_value ->
            let new_ty = ty_freevars Stv.empty ty_value in
            Stv.fold add new_ty (vars,Mtv.empty) in
      (match expr with
      | Term t ->
          let t = term_transform kept varM t in
          Decl.make_fs_defn new_lsymbol vars t
      | Fmla f ->
          let f = fmla_transform kept varM f in
          Decl.make_ps_defn new_lsymbol vars f)
    | (lsymbol, None) ->
      (findL lsymbol, None)
    in
    let l = List.fold_left
      (fun acc (lsymbol,_) -> logic_guard kept acc lsymbol) [] decls in
    (Decl.create_logic_decl (List.map helper decls))::l

  (** transform an inductive declaration *)
  let ind_transform kept idl =
    let iconv (pr,f) = pr, Libencoding.f_type_close (fmla_transform kept) f in
    let conv (ls,il) = findL ls, List.map iconv il in
    [Decl.create_ind_decl (List.map conv idl)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform kept (prop_kind, prop_name, f) =
    let quantified_fmla = Libencoding.f_type_close (fmla_transform kept) f in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

let decl kept d = match d.d_node with
  | Dtype tdl -> d :: Libencoding.lsdecl_of_tydecl tdl
  | Dlogic ldl -> Transform.logic_transform kept ldl
  | Dind idl -> Transform.ind_transform kept idl
  | Dprop prop -> Transform.prop_transform kept prop

let empty_th =
  let task = use_export None Theory.builtin_theory in
  let task = Task.add_decl task d_ts_type in
  let task = Task.add_logic_decl task [Transform.fs_type,None] in
  task

let guard =
  Trans.on_tagged_ty Encoding.meta_kept (fun kept ->
    Trans.decl (decl kept) empty_th)

(** {2 monomorphise task } *)

let ts_base = create_tysymbol (id_fresh "uni") [] None
let ty_base = ty_app ts_base []

let lsmap tyb kept = Wls.memoize 63 (fun ls ->
  let tymap ty = if Sty.mem ty kept then ty else tyb in
  let ty_res = Util.option_map tymap ls.ls_value in
  let ty_arg = List.map tymap ls.ls_args in
  if Util.option_eq ty_equal ty_res ls.ls_value &&
     List.for_all2 ty_equal ty_arg ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res)

let d_ts_base = create_ty_decl [ts_base, Tabstract]

let monomorph tyb = Trans.on_tagged_ty Encoding.meta_kept (fun kept ->
  let kept = Sty.add ty_type kept in
  let tyb = match tyb.ty_node with
    | Tyapp (_,[]) when not (Sty.mem tyb kept) -> tyb
    | _ -> ty_base
  in
  let decl = Libencoding.d_monomorph tyb kept (lsmap tyb kept) in
  Trans.decl decl (Task.add_decl None d_ts_base))

let monomorph = Trans.on_meta_excl Encoding.meta_base (fun alo ->
  let tyb = match alo with
    | Some [Theory.MAts ts] when ts.ts_args = [] ->
        begin match ts.ts_def with
          | Some ty -> ty
          | None -> ty_app ts []
        end
    | _ -> ty_base
  in
  monomorph tyb)

let () = Trans.private_register_env Encoding.poly_pr "guard"
    (fun _ -> Trans.compose guard monomorph)
