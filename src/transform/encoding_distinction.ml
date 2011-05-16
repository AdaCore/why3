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

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task


(** Transformation "distinction" *)

let meta_lsinst = register_meta "encoding : lsinst" [MTlsymbol;MTlsymbol]
let meta_kept   = register_meta "encoding : kept"   [MTty]

module Env = struct


(* TODO : transmettre les tags des logiques polymorphe vers les logiques
   instantié. Un tag sur un logique polymorphe doit être un tag sur toute
   la famille de fonctions *)

  module OHTy = OrderedHash(struct
    type t = ty
    let tag = ty_hash
  end)

  module OHTyl = OrderedHashList(struct
    type t = ty
    let tag = ty_hash
  end)

  module Mtyl = Map.Make(OHTyl)
  module Htyl = Hashtbl.Make(OHTyl)

  (* The environnement of the transformation between two decl *)
  type env = lsymbol Mtyl.t Mls.t

  let empty_env = Mls.empty

  let print_env fmt menv =
    Format.fprintf fmt "defined_lsymbol (%a)@."
      (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
         (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
            (Pp.print_list Pp.space Pretty.print_ty)
            Pretty.print_ls)) menv

  (** From/To metas *)
  let metas_of_env env decls =
    let fold_ls ls insts metas =
      let fold_inst _ lsinst metas =
        create_meta meta_lsinst [Theory.MAls ls;Theory.MAls lsinst] :: metas
      in
      Mtyl.fold fold_inst insts metas
    in
    Mls.fold fold_ls env decls

  let env_of_metas metas =
    let fold env args =
      match args with
        | [MAls ls;MAls lsinst] ->
          let tydisl = option_apply lsinst.ls_args (fun e -> e::lsinst.ls_args)
            lsinst.ls_value
          in
          let insts = Mls.find_default ls Mtyl.empty env in
          Mls.add ls (Mtyl.add tydisl lsinst insts) env
        | _ -> assert false
    in
    List.fold_left fold Mls.empty metas

end

open Env

(* Ce type est utiliser pour indiquer un underscore *)
let tv_dumb = create_tvsymbol (id_fresh "Dumb")
let ty_dumb = ty_var tv_dumb

let find_logic env p tl tyv =
  if ls_equal p ps_equ then p else
    try
      let insts = Mls.find p env in
      let inst = option_apply tl (fun e -> e::tl) tyv in
      Mtyl.find inst insts
    with Not_found -> p

let conv_vs tvar vsvar vs =
  let ty = ty_inst tvar vs.vs_ty in
  let vs' = if ty_equal ty vs.vs_ty then vs else
      create_vsymbol (id_clone vs.vs_name) ty in
  Mvs.add vs (t_var vs') vsvar,vs'

(* The convertion of term and formula *)
let rec rewrite_term env tvar vsvar t =
  let fnT = rewrite_term env tvar in
  let fnF = rewrite_fmla env tvar in
  (* Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t; *)
  let t = match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
      let tl = List.map (fnT vsvar) tl in
      let ty = oty_inst tvar t.t_ty in
      let p = find_logic env p (List.map t_type tl) ty in
      t_app p tl ty
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) ->
      let u,t2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs tvar vsvar u in
      let t1 = fnT vsvar t1 in let t2 = fnT vsvar' t2 in
      t_let t1 (cb u t2)
    | Tcase _ | Teps _ ->
      Printer.unsupportedTerm t
        "Encoding arrays : I can't encode this term"
    | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)
  in
  (* Format.eprintf "@[<hov 2>Term : => %a : %a@\n@?" *)
  (*   Pretty.print_term t Pretty.print_ty t.t_ty; *)
  t

and rewrite_fmla env tvar vsvar f =
  let fnT = rewrite_term env tvar in
  let fnF = rewrite_fmla env tvar in
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  match f.t_node with
    | Tapp(p, tl) ->
      let tl = List.map (fnT vsvar) tl in
      let p = find_logic env p (List.map t_type tl) None in
      ps_app p tl
    | Tquant(q, b) ->
      let vl, tl, f1, cb = t_open_quant_cb b in
      let vsvar,vl = map_fold_left (conv_vs tvar) vsvar vl in
      let f1 = fnF vsvar f1 in
      let tl = TermTF.tr_map (fnT vsvar) (fnF vsvar) tl in
      t_quant q (cb vl tl f1)
    | Tlet (t1, b) -> let u,f2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs tvar vsvar u in
      let t1 = fnT vsvar t1 and f2 = fnF vsvar' f2 in
      (* Format.eprintf "u.vs_ty : %a == t1.t_ty : %a@." *)
      (*    Pretty.print_ty u.vs_ty Pretty.print_ty t1.t_ty; *)
      Ty.ty_equal_check u.vs_ty (t_type t1);
      t_let t1 (cb u f2)
    | _ -> TermTF.t_map (fun _ -> assert false) (fnF vsvar) f


module Ssubst =
  Set.Make(struct type t = ty Mtv.t
                  let compare = Mtv.compare OHTy.compare end)

(* find all the possible instantiation which can create a kept instantiation *)
let ty_quant env =
  let rec add_vs acc0 ls tyl tyv =
    if ls_equal ls ps_equ then acc0 else
      try
        let insts = Mls.find ls env in
        let tyl = option_apply tyl (fun e -> e::tyl) tyv in
        let fold_inst inst _ acc =
          let fold_subst subst acc =
            try
              let subst = List.fold_left2 ty_match subst tyl inst  in
              Ssubst.add subst acc
            with TypeMismatch _ -> acc
          in
          (* fold on acc0 *)
          Ssubst.fold fold_subst acc0 acc
        in
        Mtyl.fold fold_inst insts acc0
      with Not_found (* no such p *) -> acc0
  in
  t_app_fold add_vs (Ssubst.singleton (Mtv.empty))

(* The Core of the transformation *)
let map env d =
    match d.d_node with
    | Dtype [_,Tabstract] -> [d]
    | Dtype _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn = function
          | _, Some _ ->
              Printer.unsupportedDecl
                d "encoding_decorate : I can't encode definition. \
Perhaps you could use eliminate_definition"
          | _, None -> () in
            List.iter fn l; [d]
    | Dind _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
      let substs = ty_quant env f in
      let substs_len = Ssubst.cardinal substs in
      let conv_f tvar task =
        (* Format.eprintf "f0 : %a@. env : %a@." Pretty.print_fmla *)
        (*   (t_ty_subst tvar Mvs.empty f) *)
        (*   print_env env; *)
        let f = rewrite_fmla env tvar Mvs.empty f in
        (* Format.eprintf "f : %a@. env : %a@." Pretty.print_fmla f *)
        (*   print_env menv; *)
        let pr =
          if substs_len = 1 then pr
          else create_prsymbol (id_clone pr.pr_name) in
        (* Format.eprintf "undef ls : %a, ts : %a@." *)
        (*   (Pp.print_iter1 Sls.iter Pp.comma Pretty.print_ls) *)
        (*   menv.undef_lsymbol *)
        (*   (Pp.print_iter1 Sts.iter Pp.comma Pretty.print_ts) *)
        (*   menv.undef_tsymbol; *)
        create_prop_decl k pr f :: task
      in
      let task = Ssubst.fold conv_f substs [] in
      task

let definition_of_env env =
  let fold_ls _ insts task =
    let fold_inst inst lsinst task =
      let fold_ty task ty =
        let add_ts task ts = add_ty_decl task ([ts,Tabstract]) in
        ty_s_fold add_ts task ty in
      let task = List.fold_left fold_ty task inst in
      add_logic_decl task [lsinst,None]
    in
    Mtyl.fold fold_inst insts task
  in
  Mls.fold fold_ls env (Task.use_export None (Theory.builtin_theory))

let lsymbol_distinction =
  Trans.on_meta meta_lsinst (fun metas ->
    if metas = [] then Trans.identity
    else
      let env = env_of_metas metas in
      (* Format.eprintf "instantiate %a@." print_env env; *)
      Trans.decl (map env) (definition_of_env env))
