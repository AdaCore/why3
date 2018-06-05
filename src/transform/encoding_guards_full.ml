(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** transformation from polymorphic logic to many-sorted logic *)

open Wstdlib
open Ident
open Ty
open Term
open Decl
open Task
open Libencoding

(* complete dead module code

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
*)

(** {2 module to separate utilities from important functions} *)

module Lib = struct

(* function symbol selecting ty_type from ty_type^n *)
let ls_selects_of_ts = Wts.memoize 63 (fun ts ->
  let create_select _ =
    let preid = id_fresh ("select_"^ts.ts_name.id_string) in
    create_fsymbol preid [ty_type] ty_type in
  List.rev_map create_select ts.ts_args)

let ls_int_of_ty = create_fsymbol (id_fresh "int_of_ty") [ty_type] ty_int

(** definition of the previous selecting functions *)
let ls_selects_def_of_ts acc ts =
  let ls = ls_of_ts ts in
  let vars = List.rev_map
    (fun _ -> create_vsymbol (id_fresh "x") ty_type) ts.ts_args
  in
  let tvars = List.map t_var vars in
  (* type to int *)
  let id = id_hash ts.ts_name in
  let acc =
    let t = fs_app ls tvars ty_type in
    let f = t_equ (fs_app ls_int_of_ty [t] ty_int) (t_nat_const id) in
    let f = t_forall_close vars [[t]] f in
    let prsymbol = create_prsymbol (id_clone ts.ts_name) in
    create_prop_decl Paxiom prsymbol f :: acc
  in
  (* select *)
  let ls_selects = ls_selects_of_ts ts in
  let fmlas = List.rev_map2
    (fun ls_select value ->
      let t = fs_app ls tvars ty_type in
      let t = fs_app ls_select [t] ty_type in
      let f = t_equ t value in
      let f = t_forall_close vars [[t]] f in
      f)
    ls_selects tvars in
  let create_props ls_select fmla =
    let prsymbol = create_prsymbol (id_clone ls_select.ls_name) in
    create_prop_decl Paxiom prsymbol fmla in
  let props =
    List.fold_left2 (fun acc x y -> create_props x y::acc)
      acc ls_selects fmlas in
  let add acc fs = create_param_decl fs :: acc in
  List.fold_left add props ls_selects

(* convert a type declaration to a list of lsymbol declarations *)
let lsdecl_of_ts_select ts =
  let defs = ls_selects_def_of_ts [] ts in
  create_param_decl (ls_of_ts ts) :: defs

end

module Transform = struct

  (** type_of *)
  let fs_type =
    let alpha = ty_var (create_tvsymbol (id_fresh "a")) in
    create_fsymbol (id_fresh "type_of") [alpha] ty_type

  let app_type t = fs_app fs_type [t] ty_type

  (** rewrite a closed formula modulo its free typevars
      using selection functions *)
  let rec extract_tvar acc t ty = match ty.ty_node with
    | Tyvar tvar when Mtv.mem tvar acc -> acc
    | Tyvar tvar -> Mtv.add tvar t acc
    | Tyapp (ts,tyl) ->
      let fold acc ls_select ty =
        extract_tvar acc (fs_app ls_select [t] ty_type) ty in
      List.fold_left2 fold acc (Lib.ls_selects_of_ts ts) tyl

  let type_close_select tvs ts fn f =
    let fold acc t = extract_tvar acc (app_type t) (t_type t) in
    let tvm = List.fold_left fold Mtv.empty ts in
    let tvs = Mtv.set_diff tvs tvm in
    let get_vs tv = create_vsymbol (id_clone tv.tv_name) ty_type in
    let tvm' = Mtv.mapi (fun v () -> get_vs v) tvs in
    let vl = Mtv.values tvm' in
    let tvm' = Mtv.map t_var tvm' in
    let tvm = Mtv.union (fun _ _ _ -> assert false) tvm tvm' in
    t_forall_close_simp vl [] (fn tvm f)


  let type_variable_only_in_value lsymbol =
    let tvar_val = ty_freevars Stv.empty (Opt.get lsymbol.ls_value) in
    let tvar_arg = List.fold_left ty_freevars Stv.empty lsymbol.ls_args in
    Stv.diff tvar_val tvar_arg

  (** creates a new logic symbol, with a different type if the
  given symbol was polymorphic *)
  let findL = Wls.memoize 63 (fun lsymbol ->
    if lsymbol.ls_value = None then lsymbol else
    let new_ty = type_variable_only_in_value lsymbol in
    (* as many t as type vars *)
    if Stv.is_empty new_ty then lsymbol (* same type *) else
      let add _ acc = ty_type :: acc in
      let args = Stv.fold add new_ty lsymbol.ls_args in
      (* creates a new lsymbol with the same name but a different type *)
      Term.create_lsymbol (id_clone lsymbol.ls_name) args lsymbol.ls_value)

  (* {1 transformations} *)
    (** todo use callback for this one *)
  let rec f_open_all_quant q f = match f.t_node with
    | Tquant (q', f) when q' = q ->
      let vl, tr, f = t_open_quant f in
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
      (* first case : predicate are not translated *)
    | Tapp(p,terms) when t.t_ty = None ->
      let terms = List.map (term_transform kept varM) terms in
      ps_app (findL p) terms
    | Tapp(f,terms) ->
      let terms = args_transform kept varM f terms (t_type t) in
      t_app (findL f) terms t.t_ty
    | Tquant(q,_) ->
      let vsl,trl,fmla = f_open_all_quant q t in
      let fmla = term_transform kept varM fmla in
      let fmla2 = guard q kept varM fmla vsl in
        (* TODO : how to modify the triggers? *)
      let trl = tr_map (term_transform kept varM) trl in
      t_quant q (t_close_quant vsl trl fmla2)
    | _ -> (* default case : traverse *)
      t_map (term_transform kept varM) t

  and guard q kept varM fmla vsl =
    let aux fmla vs =
      if Libencoding.is_protected_vs kept vs then fmla else
        let g = t_equ (app_type (t_var vs)) (term_of_ty varM vs.vs_ty) in
        match q with
          | Tforall -> t_implies g fmla
          | Texists -> t_and g fmla in
    List.fold_left aux fmla vsl

  and args_transform kept varM lsymbol args ty =
    (* Debug.print_list Pretty.print_ty Format.std_formatter type_vars; *)
    let tv_to_ty = ty_match Mtv.empty (Opt.get lsymbol.ls_value) ty in
    let new_ty = type_variable_only_in_value lsymbol in
    let tv_to_ty = Mtv.set_inter tv_to_ty new_ty in
    (* Debug.print_mtv Pretty.print_ty Format.err_formatter tv_to_ty; *)
    let args = List.map (term_transform kept varM) args in
    (* fresh args to be added at the beginning of the list of arguments *)
    let add _ ty acc = term_of_ty varM ty :: acc in
    Mtv.fold add tv_to_ty args

  let f_type_close_select kept f' =
    let tvs = t_ty_freevars Stv.empty f' in
    let trans fn acc f = match f.t_node with
      | Tquant(Tforall as q,_) -> (* Exists same thing? *)
        let vsl,trl,fmla = f_open_all_quant q f in
        let add acc vs = (t_var vs)::acc in
        let acc = List.fold_left add acc vsl in
        let fn varM f =
          let fmla2 = guard q kept varM f vsl in
          (* TODO : how to modify the triggers? *)
          let trl = tr_map (term_transform kept varM) trl in
          fn varM (t_quant q (t_close_quant vsl trl fmla2))
        in
        let fn varM f = fn varM (term_transform kept varM f) in
        type_close_select tvs acc fn fmla
      | _ ->
        let fn varM f = fn varM (term_transform kept varM f) in
        type_close_select tvs acc fn f in
    trans (fun _ f -> f) [] f'

  let logic_guard kept acc lsymbol =
    match lsymbol.ls_value with
      | None -> acc
      | Some _ when Libencoding.is_protected_ls kept lsymbol -> acc
      | Some ty_val ->
        let v_id = if Libencoding.is_protecting_id lsymbol.ls_name
          then id_fresh "x" else Libencoding.id_unprotected "j" in
        let varl = List.map (create_vsymbol v_id) lsymbol.ls_args in
        let trans varM () =
          let terms = List.map t_var varl in
          let terms = args_transform kept varM lsymbol terms ty_val in
          let fmla =
            t_equ (app_type (fs_app (findL lsymbol) terms ty_val))
              (term_of_ty varM ty_val) in
          let guard fmla vs =
            if Libencoding.is_protected_vs kept vs then fmla else
              let g = t_equ (app_type (t_var vs)) (term_of_ty varM vs.vs_ty) in
              t_implies g fmla in
          let fmla = List.fold_left guard fmla varl in
          t_forall_close_simp varl [] fmla
        in
        let stv = ls_ty_freevars lsymbol in
        let tl = List.rev_map (t_var) varl in
        let fmla = type_close_select stv tl trans () in
        Decl.create_prop_decl Paxiom
          (create_prsymbol (id_clone lsymbol.ls_name)) fmla::acc

  let param_transform kept ls =
    Decl.create_param_decl (findL ls) :: logic_guard kept [] ls

  let logic_transform kept d = function
    | [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
        let f = f_type_close_select kept (ls_defn_axiom ld) in
        Libencoding.defn_or_axiom (findL ls) f @ logic_guard kept [] ls
    | _ -> Printer.unsupportedDecl d
        "Recursively-defined symbols are not supported, run eliminate_recursion"

  (** transform an inductive declaration *)
  let ind_transform kept s idl =
    let iconv (pr,f) = pr, f_type_close_select kept f in
    let conv (ls,il) = findL ls, List.map iconv il in
    [Decl.create_ind_decl s (List.map conv idl)]

  (** transforms a proposition into another (mostly a substitution) *)
  let prop_transform kept (prop_kind, prop_name, f) =
    let quantified_fmla = f_type_close_select kept f in
    [Decl.create_prop_decl prop_kind prop_name quantified_fmla]

end

(** {2 main part} *)

let decl kept d = match d.d_node with
  | Dtype { ts_def = Alias _ } -> []
  | Dtype ts -> d :: Lib.lsdecl_of_ts_select ts
  | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic types are not supported, run eliminate_algebraic"
  | Dparam ls -> Transform.param_transform kept ls
  | Dlogic ldl -> Transform.logic_transform kept d ldl
  | Dind (s, idl) -> Transform.ind_transform kept s idl
  | Dprop prop -> Transform.prop_transform kept prop

let empty_th =
  let task = use_export None Theory.builtin_theory in
  let task = Task.add_decl task d_ts_type in
  let task = Task.add_param_decl task Lib.ls_int_of_ty in
  let task = Task.add_param_decl task Transform.fs_type in
  task

let guard =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
    Trans.decl (decl kept) empty_th)

let () = Hstr.replace Encoding.ft_enco_poly "guards_full"
    (fun _ -> Trans.compose guard Libencoding.monomorphise_task)
