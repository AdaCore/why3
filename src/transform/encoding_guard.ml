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

  (** type_of *)
  let fs_type =
    let alpha = ty_var (create_tvsymbol (id_fresh "a")) in
    create_fsymbol (id_fresh "type_of") [alpha] ty_type

  let app_type t = t_app fs_type [t] ty_type

  (** rewrite a closed formula modulo its free typevars
      using selection functions *)
  let rec extract_tvar acc t ty = match ty.ty_node with
    | Tyvar tvar when Mtv.mem tvar acc -> acc
    | Tyvar tvar -> Mtv.add tvar t acc
    | Tyapp (ts,tyl) ->
      let fold acc ls_select ty =
        extract_tvar acc (t_app ls_select [t] ty_type) ty in
      List.fold_left2 fold acc (ls_selects_of_ts ts) tyl

  let type_close_select tvs ts fn f =
    let fold acc t = extract_tvar acc (app_type t) (t_type t) in
    let tvm = List.fold_left fold Mtv.empty ts in
    let tvs = Mtv.diff (const3 None) tvs tvm in
    let get_vs tv = create_vsymbol (id_clone tv.tv_name) ty_type in
    let tvm' = Mtv.mapi (fun v () -> get_vs v) tvs in
    let vl = Mtv.values tvm' in
    let tvm' = Mtv.map t_var tvm' in
    let tvm = Mtv.union (fun _ _ _ -> assert false) tvm tvm' in
    f_forall_close_simp vl [] (fn tvm f)


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
    (** todo use callback for this one *)
  let rec f_open_all_quant q f = match f.t_node with
    | Fquant (q', f) when q' = q ->
      let vl, tr, f = f_open_quant f in
      begin match tr with
        | [] ->
          let vl', tr, f = f_open_all_quant q f in
          vl@vl', tr, f
        | _ -> vl, tr, f
      end
    | _ -> [], [], f


  (** translation of terms *)
  let rec term_transform kept varM t =
    match t.t_node with
    | Tapp(f, terms) ->
      let terms = args_transform kept varM f terms (t_type t) in
      e_app (findL f) terms t.t_ty
    | _ -> (* default case : traverse *)
      t_map (term_transform kept varM) (fmla_transform kept varM) t

  (** translation of formulae *)
  and fmla_transform kept varM f =
    match f.t_node with
      (* first case : predicate are not translated *)
    | Tapp(p,terms) ->
      let terms = List.map (term_transform kept varM) terms in
      f_app (findL p) terms
    | Fquant(q,_) ->
      let vsl,trl,fmla = f_open_all_quant q f in
      let fmla = fmla_transform kept varM fmla in
      let fmla2 = guard q kept varM fmla vsl in
        (* TODO : how to modify the triggers? *)
      let trl = tr_map (term_transform kept varM)
        (fmla_transform kept varM) trl in
      f_quant q (f_close_quant vsl trl fmla2)
    | _ -> (* otherwise : just traverse and translate *)
      f_map (term_transform kept varM) (fmla_transform kept varM) f(*   in *)
    (* Format.eprintf "fmla_to : %a@." Pretty.print_fmla f;f *)

  and guard q kept varM fmla vsl =
    let aux fmla vs =
      if Sty.mem vs.vs_ty kept then fmla else
        let g = f_equ (app_type (t_var vs)) (term_of_ty varM vs.vs_ty) in
        match q with
          | Fforall -> f_implies g fmla
          | Fexists -> f_and g fmla in
    List.fold_left aux fmla vsl

  and args_transform kept varM lsymbol args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ty_match Mtv.empty (of_option lsymbol.ls_value) ty in
    let new_ty = type_variable_only_in_value lsymbol in
    let tv_to_ty = Mtv.inter (fun _ tv () -> Some tv) tv_to_ty new_ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform kept varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = term_of_ty varM ty :: acc in
    Mtv.fold add tv_to_ty args

  and f_type_close_select kept f' =
    let tvs = f_ty_freevars Stv.empty f' in
    let rec trans fn acc f = match f.t_node with
      | Fquant(Fforall as q,_) -> (* Exists same thing? *)
        let vsl,trl,fmla = f_open_all_quant q f in
        let add acc vs = (t_var vs)::acc in
        let acc = List.fold_left add acc vsl in
        let fn varM f =
          let fmla2 = guard q kept varM f vsl in
          (* TODO : how to modify the triggers? *)
          let trl = tr_map (term_transform kept varM)
            (fmla_transform kept varM) trl in
          fn varM (f_quant q (f_close_quant vsl trl fmla2))
        in
        let fn varM f = fn varM (fmla_transform kept varM f) in
        type_close_select tvs acc fn fmla
      | _ ->
        let fn varM f = fn varM (fmla_transform kept varM f) in
        type_close_select tvs acc fn f in
    trans (fun _ f -> f) [] f'

  let logic_guard kept acc lsymbol =
    match lsymbol.ls_value with
      | None -> acc
      | Some ty_val when Sty.mem ty_val kept -> acc
      | Some ty_val ->
        let varl = List.map (fun v -> create_vsymbol (id_fresh "x") v)
          lsymbol.ls_args in
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
        let stv = ls_ty_freevars lsymbol in
        let tl = List.rev_map (t_var) varl in
        let fmla = type_close_select stv tl trans () in
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
        vs :: vl, Mtv.add v (t_var vs) vm
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
    let iconv (pr,f) = pr, f_type_close_select kept f in
    let conv (ls,il) = findL ls, List.map iconv il in
    [Decl.create_ind_decl (List.map conv idl)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform kept (prop_kind, prop_name, f) =
    let quantified_fmla = f_type_close_select kept f in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

let decl kept d = match d.d_node with
  | Dtype tdl -> d :: Libencoding.lsdecl_of_tydecl_select tdl
  | Dlogic ldl -> Transform.logic_transform kept ldl
  | Dind idl -> Transform.ind_transform kept idl
  | Dprop prop -> Transform.prop_transform kept prop

let empty_th =
  let task = use_export None Theory.builtin_theory in
  let task = Task.add_decl task d_ts_type in
  let task = Task.add_logic_decl task [ls_int_of_ty,None] in
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

let () = Hashtbl.replace Encoding.ft_enco_poly "guard"
    (fun _ -> Trans.compose guard monomorph)
