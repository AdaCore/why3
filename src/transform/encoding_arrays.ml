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
open Task
open Theory
open Task
open Decl
open Encoding


(* Ce type est utiliser pour indiquer un underscore *)
let tv_dumb = create_tvsymbol (id_fresh "Dumb")
let ty_dumb = ty_var tv_dumb

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

(* The environnement of the transformation between two decl (* unmutable *) *)
type env = lsymbol Mtyl.t Mls.t

let print_env fmt menv =
  Format.fprintf fmt "defined_lsymbol (%a)@."
    (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ls)) menv

(* let create_arrays th = *)
(*   { *)
(*     theory = th; *)
(*     get = ns_find_ls th.th_export ["get"]; *)
(*     set = ns_find_ls th.th_export ["set"]; *)
(*     t = ty_app (ns_find_ts th.th_export ["t"]) []; *)
(*     key = ty_app (ns_find_ts th.th_export ["key"]) []; *)
(*     value = ty_app (ns_find_ts th.th_export ["value"]) []; *)
(*   } *)

(*
let find_arrays menv ty =
  (* try *)
    Mty.find ty menv.arrays
  (* with Not_found when Sty.mem ty menv.keep  -> *)
  (*   let key,value = *)
  (*     match ty.ty_node with *)
  (*       | Tyapp (_,[key;value]) -> key,value *)
  (*       | _ -> assert false in *)
  (*   let th_uc = create_theory (id_clone menv.clonable_theory.th_name) in *)
  (*   (\* temporary tsymbol *\) *)
  (*   let th_inst = create_inst ~ts:[menv.clonable_key,key; *)
  (*                                  menv.clonable_value,value] ~ls:[] *)
  (*     ~lemma:[] ~goal:[] in *)
  (*   let th_uc = clone_export th_uc menv.clonable th_inst in *)
  (*   let th = close_theory th_uc in *)
  (*   let arrays = create_arrays th in *)
  (*   menv.arrays <- Mty.add ty arrays menv.arrays; *)
  (*   menv.undef_arrays <- Sty.add ty menv.undef_arrays; *)
  (*   arrays *)
*)

let find_logic env p tl tyv =
  if ls_equal p ps_equ then p else
    try
      let insts = Mls.find p env in
      let inst = option_apply tl (fun e -> e::tl) tyv in
      Mtyl.find inst insts
    with Not_found -> p

(* let find_logic env p tl tyv = *)
(*   let p2 = find_logic env p tl tyv in *)
(*   Format.eprintf "p : %a, tl : %a, tv : %a,  p2 : %a@." *)
(*     Pretty.print_ls p *)
(*     (Pp.print_list Pp.space Pretty.print_ty) tl *)
(*     (Pp.print_option Pretty.print_ty) tyv *)
(*     Pretty.print_ls p2; *)
(*   p2 *)

(* let find_logic menv tvar p tl tyv = *)
(*   if ls_equal p ps_equ then p else begin *)
(*     (\** project the type on : keep + {dumb} *\) *)
(*     let to_dumb {t_ty = ty} = *)
(*       let ty = ty_inst tvar ty in *)
(*       Mty.find_default ty ty_dumb menv.env.keep in *)
(*     let inst_l = List.map to_dumb tl in *)
(*     let inst_tyv = option_map to_dumb tyv in *)
(*     let inst_l_tyv = option_apply inst_l (fun e -> e::inst_l) inst_tyv in *)
(*     (\* Format.eprintf "env : %ap : %a | arg : %a| tyl = %a | inst_l : %a@."
 *\) *)
(*     (\*   print_env menv *\) *)
(*     (\*   Pretty.print_ls p *\) *)
(*     (\*   (Pp.print_list Pp.comma Pretty.print_ty) p.ls_args *\) *)
(*     (\*   (Pp.print_list Pp.comma Pretty.print_ty) *\) *)
(*     (\*   (List.map (fun t -> ty_inst tvar t.t_ty) tl) *\) *)
(*     (\*   (Pp.print_list Pp.comma Pretty.print_ty) inst_l_tyv; *\) *)
(*     try *)
(*       let insts = Mls.find p menv.defined_lsymbol in *)
(*       Mtyl.find inst_l_tyv insts *)
(*     with Not_found -> *)
(*       let insts = Mls.find_default p Mtyl.empty menv.defined_lsymbol in *)
(*       let to_new tyd ty = if ty_equal tyd ty_dumb then ty else tyd in *)
(*       let arg = List.map2 to_new inst_l p.ls_args in *)
(*       let value = option_map2 to_new inst_tyv p.ls_value in *)
(*       let ls = if List.for_all2 ty_equal arg p.ls_args && *)
(*           option_eq ty_equal value p.ls_value *)
(*         then p else clone_lsymbol p arg value in *)
(*       let insts = Mtyl.add inst_l_tyv ls insts in *)
(*       menv.defined_lsymbol <- Mls.add p insts menv.defined_lsymbol; *)
(*       menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol; *)
(*       ls *)
(*   end *)

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
      let p = find_logic env p (List.map (fun t -> t.t_ty) tl)
        (Some (ty_inst tvar t.t_ty)) in
      t_app p tl (ty_inst tvar t.t_ty)
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) ->
      let u,t2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs tvar vsvar u in
      let t1 = fnT vsvar t1 in let t2 = fnT vsvar' t2 in
      t_let t1 (cb u t2)
    | Tcase _ | Teps _ ->
      Printer.unsupportedTerm t
        "Encoding arrays : I can't encode this term" in
  (* Format.eprintf "@[<hov 2>Term : => %a : %a@\n@?" *)
  (*   Pretty.print_term t Pretty.print_ty t.t_ty; *)
  t

and rewrite_fmla env tvar vsvar f =
  let fnT = rewrite_term env tvar in
  let fnF = rewrite_fmla env tvar in
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  match f.f_node with
    | Fapp(p, tl) ->
      let tl = List.map (fnT vsvar) tl in
      let p = find_logic env p (List.map (fun t -> t.t_ty) tl) None in
      f_app p tl
    | Fquant(q, b) ->
      let vl, tl, f1, cb = f_open_quant_cb b in
      let vsvar,vl = map_fold_left (conv_vs tvar) vsvar vl in
      let f1 = fnF vsvar f1 in
      let tl = tr_map (fnT vsvar) (fnF vsvar) tl in
      f_quant q (cb vl tl f1)
    | Flet (t1, b) -> let u,f2,cb = f_open_bound_cb b in
      let (vsvar',u) = conv_vs tvar vsvar u in
      let t1 = fnT vsvar t1 and f2 = fnF vsvar' f2 in
      (* Format.eprintf "u.vs_ty : %a == t1.t_ty : %a@." *)
      (*    Pretty.print_ty u.vs_ty Pretty.print_ty t1.t_ty; *)
      assert (u.vs_ty == t1.t_ty);
      f_let t1 (cb u f2)
    | _ -> f_map (fun _ -> assert false) (fnF vsvar) f


module Ssubst =
  Set.Make(struct type t = ty Mtv.t
                  let compare = Mtv.compare OHTy.compare end)


(* (\* Generation of all the possible instantiation of a formula *\) *)
(* let gen_tvar su = *)
(*   (\* Try to apply one subst on all the other subst generated until then *)
(*      (ie. in su), that give newly generated subst (ie to put in su)*\) *)
(*   let aux subst su = *)
(*     (\* filter the possible application of substitution *\) *)
(*     let disj_union m1 m2 = Mtv.union (fun _ ty1 ty2 -> *)
(*       if ty_equal ty1 ty2 then Some ty1 else raise Exit) m1 m2 in *)
(*     let fold subst1 acc = *)
(*       try Ssubst.add (disj_union subst1 subst) acc with Exit -> acc in *)
(*     Ssubst.fold fold su su in *)
(*   Ssubst.fold aux su (Ssubst.singleton (Mtv.empty)) *)

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
  f_app_fold add_vs (Ssubst.singleton (Mtv.empty))

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
        (*   (f_ty_subst tvar Mvs.empty f) *)
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

let meta_lskept = register_meta "encoding : lskept" [MTlsymbol]

let env_from_kept_lskept kept lskept =
  let fold_ls ls env =
    let rec aux insts tydisl subst = function
      | [] ->
        let tydisl = List.rev tydisl in
        let tyl,tyv = match tydisl, ls.ls_value with
          | tyv::tyl, Some _ -> tyl,Some tyv
          | tyl, None -> tyl,None
          | _ -> assert false in
        let lsdis = create_lsymbol (id_clone ls.ls_name) tyl tyv in
        Mtyl.add tydisl lsdis insts
      | ty::tyl ->
        let fold_ty tykept insts =
          try
            let subst = ty_match subst ty tykept in
            aux insts (tykept::tydisl) subst tyl
          with TypeMismatch _ -> insts
        in
        Sty.fold fold_ty kept insts
    in
    let lsty = option_apply ls.ls_args (fun e -> e::ls.ls_args) ls.ls_value in
    let insts = aux Mtyl.empty  [] Mtv.empty lsty in
    Mls.add ls insts env
  in
  Sls.fold fold_ls lskept Mls.empty

let is_ty_mono ty =
  try
    let rec check () ty = match ty.ty_node with
      | Tyvar _ -> raise Exit
      | Tyapp _ -> ty_fold check () ty in
    check () ty;
    true
  with Exit -> false

let meta_lsdis = register_meta "encoding : lsdis" [MTlsymbol;MTlsymbol]

let metas_of_env env decls =
  let fold_ls ls insts metas =
    let fold_inst _ lsdis metas =
      create_meta meta_lsdis [Theory.MAls ls;Theory.MAls lsdis] :: metas
    in
    Mtyl.fold fold_inst insts metas
  in
  Mls.fold fold_ls env decls

let env_of_metas metas =
  let fold env args =
    match args with
      | [MAls ls;MAls lsdis] ->
        let tydisl = option_apply lsdis.ls_args (fun e -> e::lsdis.ls_args)
          lsdis.ls_value
        in
        let insts = Mls.find_default ls Mtyl.empty env in
        Mls.add ls (Mtyl.add tydisl lsdis insts) env
      | _ -> assert false
  in
  List.fold_left fold Mls.empty metas

let env_from_fold lskept (env,kept) ls tyl tyv =
  if Sls.mem ls lskept &&
    List.for_all is_ty_mono tyl && option_apply true is_ty_mono tyv then
    let tydisl = option_apply tyl (fun e -> e::tyl) tyv
    in
    let lsdis = create_lsymbol (id_clone ls.ls_name) tyl tyv in
    let insts = Mls.find_default ls Mtyl.empty env in
    Mls.add ls (Mtyl.add tydisl lsdis insts) env,
    List.fold_left (fun acc ty -> Sty.add ty acc) kept tydisl
  else (env,kept)

let mono_in_goal lskept pr f =
  let _,kept = f_app_fold (env_from_fold lskept) (Mls.empty,Sty.empty) f in
  let env = env_from_kept_lskept kept lskept in
  (* Format.eprintf "mono_in_goal %a@." print_env env; *)
  metas_of_env env [create_decl (create_prop_decl Pgoal pr f)]

let mono_in_goal sls = Trans.tgoal (mono_in_goal sls)

let definition_of_env env =
  let fold_ls _ insts task =
    let fold_inst inst lsdis task =
      let fold_ty task ty =
        let add_ts task ts = add_ty_decl task ([ts,Tabstract]) in
        let task = ty_s_fold add_ts task ty in
        add_meta task Encoding.meta_kept [MAty ty] in
      let task = List.fold_left fold_ty task inst in
      add_logic_decl task [lsdis,None]
    in
    Mtyl.fold fold_inst insts task
  in
  Mls.fold fold_ls env (Task.use_export None (Theory.builtin_theory))

let select_array_symbol_in_goal =
  Trans.compose Encoding.monomorphise_goal
  (Trans.on_tagged_ls meta_lskept (fun lskept ->
    if not (Sls.is_empty lskept)
    then mono_in_goal lskept
    else Trans.identity))

let () = Trans.register_transform
  "select_array_symbol_in_goal" select_array_symbol_in_goal


let instantiate_lsymbol =
  Trans.on_meta meta_lsdis (fun metas ->
    if metas = [] then Trans.identity
    else
      let env = env_of_metas metas in
      (* Format.eprintf "instantiate %a@." print_env env; *)
      Trans.decl (map env) (definition_of_env env))

let instantiate_lsymbol =
  Trans.compose (Trans.print_meta Encoding.debug meta_lsdis)
    instantiate_lsymbol

let () = Trans.register_transform
  "instantiate_lsymbol" instantiate_lsymbol

let meta_mono_array = register_meta "encoding_arrays : mono_arrays"
  [MTtysymbol;MTty;MTty]
(*
(* Some general env creation function *)
let create_env env task thpoly tds =
  let pget = ns_find_ls thpoly.th_export ["get"] in
  let pset = ns_find_ls thpoly.th_export ["set"] in
  let pt = ns_find_ts thpoly.th_export ["t"] in
  (* let pkey = ns_find_ts thpoly.th_export ["key"] in *)
  (* let pvalue = ns_find_ts thpoly.th_export ["value"] in *)
  (* Clonable theories of arrays *)
  let thclone = Env.find_theory env ["transform";"array"] "Array" in
  let cget = ns_find_ls thclone.th_export ["get"] in
  let cset = ns_find_ls thclone.th_export ["set"] in
  let ct = ns_find_ts thclone.th_export ["t"] in
  let ckey = ns_find_ts thclone.th_export ["key"] in
  let celt = ns_find_ts thclone.th_export ["elt"] in
  let clone_arrays ty _ (task,lsdefined) =
    let key,elt =
      match ty.ty_node with
        | Tyapp (_,[key;elt]) -> key,elt
        | _ -> assert false in
    (** create needed alias for the instantiation *)
    let add_ty task ty =
      match ty.ty_node with
        | Tyapp (ts,[]) -> task,ts
        | _ ->
          let ts = create_tysymbol (id_fresh "alias for clone") [] (Some ty) in
          add_ty_decl task [ts,Tabstract],ts in
    let task,tskey = add_ty task key in
    let task,tselt = add_ty task elt in
    let ts_name = "bta_"^(Pp.string_of_wnl Pretty.print_ty ty) in
    let ts = create_tysymbol (id_fresh ts_name) [] None in
    let task = add_ty_decl task [ts,Tabstract] in
    let th_inst = create_inst ~ts:[ct,ts; ckey,tskey; celt,tselt] ~ls:[]
      ~lemma:[] ~goal:[] in
    let task = Task.clone_export task thclone th_inst in
    (** Recover the subtitution *)
    let sls = match task with
      | Some {task_decl = {td_node = Clone(_,{sm_ls=sls})}} -> sls
      | _ -> assert false in
    (** type *)
    let tsy = ty_app ts [] in
    (** add get to lsdefined *)
    (** Warning result is the first element *)
    let add s = Mtyl.add [ty_dumb;tsy;ty_dumb] (Mls.find cget sls) s in
    let lsdefined = Mls.change pget
      (function | None -> Some (add Mtyl.empty) | Some s -> Some (add s))
      lsdefined in
    (** add set to lsdefined *)
    let add s = Mtyl.add [tsy;tsy;ty_dumb;ty_dumb] (Mls.find cset sls) s in
    let lsdefined = Mls.change pset
      (function | None -> Some (add Mtyl.empty) | Some s -> Some (add s))
      lsdefined in
    ((task,lsdefined),tsy) in
  (** Collect the arrays and the theory cloned *)
  let keep = collect_arrays pt tds in
  (** add the type which compose keep *)
  let task = Mty.fold (fun ty _ task ->
    let add_ts task ts = add_ty_decl task [ts,Tabstract] in
    let task = ty_s_fold add_ts task ty in
    (* let task = add_ts task ts in *)
    task (* the meta is yet here *)) keep task in
  let (task,lsdefined),keep = Mty.mapi_fold clone_arrays keep (task,Mls.empty)
  in task,{
    keep = keep;
    poly_ts = pt;
    edefined_lsymbol = lsdefined;
  }

let create_trans_complete env thpoly tds_kept =
  let init_task = use_export None builtin_theory in
  let init_task,env = create_env env init_task thpoly tds_kept in
  Trans.fold_map fold_map env init_task


let encoding_arrays env =
  let thpoly = Env.find_theory env ["array"] "Array" in
  Trans.on_used_theory thpoly (fun used ->
    if not used then Trans.identity
    else Trans.on_tagged_ts meta_kept_array (create_trans_complete env thpoly))
*)
(* This one take use the tag but also all the type which appear in the goal *)


(*
(* select the type array which appear as argument of set and get.
  set and get must be in sls *)
let find_mono_array ~only_mono sls sty f =
  let add sty ls tyl _ =
    match tyl with
      | ty::_ when Sls.mem ls sls && is_ty_mono ~only_mono ty ->
        Sty.add ty sty
      | _ -> sty in
  f_app_fold add sty f

let create_meta_ty ty =
  let name = id_fresh "meta_ty" in
  let ts = create_tysymbol name [] (Some ty) in
  (create_meta meta_kept_array [MAts ts])

let create_meta_ty = Wty.memoize 17 create_meta_ty

let create_meta_tyl sty d =
  Sty.fold (flip $ cons create_meta_ty) sty [create_decl d]

let mono_in_goal sls pr f =
  let sty = (try find_mono_array ~only_mono:true sls Sty.empty f
    with Exit -> assert false) (*monomorphise goal should have been used*) in
   create_meta_tyl sty (create_prop_decl Pgoal pr f)

let mono_in_goal sls = Trans.tgoal (mono_in_goal sls)

let trans_array th_array =
  let set = ns_find_ls th_array.th_export ["set"] in
  let get = ns_find_ls th_array.th_export ["get"] in
  let sls = Sls.add set (Sls.add get Sls.empty) in
  mono_in_goal sls

let trans_array env =
  let th_array = Env.find_theory env ["array"] "Array" in
  Trans.on_used_theory th_array (fun used ->
    if not used then Trans.identity else trans_array th_array
  )

let trans_array env = Trans.compose (trans_array env) (encoding_arrays env)

let () = Trans.register_env_transform "encoding_array" trans_array
*)
(*********************************)
(** Another way *)
(** Use partial on the subtype of arrays and twin on arrays
    (just add the twin) *)

(* select the type array which appear as argument of set and get.
  set and get must be in sls. After that take the subtype of them *)
let find_mono_array sls sty f =
  let add sty ls tyl _ =
    match tyl with
      | ty::_ when Sls.mem ls sls && is_ty_mono ty ->
        Sty.add ty sty
      | _ -> sty in
  f_app_fold add sty f

let create_meta_ty meta ty = create_meta meta [MAty ty]

let create_meta_ty meta = Wty.memoize 17 (create_meta_ty meta)

let create_meta_tyl meta =
  let cmty = create_meta_ty meta in
  fun sty d ->
    Sty.fold (flip $ cons cmty) sty d

let create_meta_tyl_arrays = create_meta_tyl meta_kept_array
let create_meta_tyl_kept = create_meta_tyl meta_kept

let subtype ty acc =
  let rec ty_add sty ty = ty_fold ty_add (Sty.add ty sty) ty in
  (* don't add the top type, only the subtype *)
  ty_fold ty_add acc ty

let mono_in_goal sls pr f =
  let sty = (try find_mono_array sls Sty.empty f
    with Exit -> assert false) (*monomorphise goal should have been used*) in
  let decls = create_meta_tyl_arrays sty
    [create_decl (create_prop_decl Pgoal pr f)] in
  let sty = Sty.fold subtype sty Sty.empty in
  create_meta_tyl_kept sty decls

let mono_in_goal sls = Trans.tgoal (mono_in_goal sls)

let select_subterm_array th_array =
  let set = ns_find_ls th_array.th_export ["set"] in
  let get = ns_find_ls th_array.th_export ["get"] in
  let sls = Sls.add set (Sls.add get Sls.empty) in
  mono_in_goal sls

(** Were all is tide together *)
open Trans
open Encoding_instantiate
let meta_arrays_to_meta_kept =
  Trans.on_tagged_ty meta_kept_array (fun sty ->
    Trans.store (function
    | Some { task_decl = td; task_prev = prev } ->
      let add ty task = add_meta task meta_kept [Theory.MAty ty] in
      let task = Sty.fold add sty prev in
      add_tdecl task td
    | _ -> assert false
    ))

(* Some general env creation function *)
let create_env_array env thpoly task tenv kept kept_array =
  let pget = ns_find_ls thpoly.th_export ["get"] in
  let pset = ns_find_ls thpoly.th_export ["set"] in
   let pt = ns_find_ts thpoly.th_export ["t"] in
  (* let pkey = ns_find_ts thpoly.th_export ["key"] in *)
  (* let pvalue = ns_find_ts thpoly.th_export ["value"] in *)
  (* Clonable theories of arrays *)
  let thclone = Env.find_theory env ["transform";"array"] "Array" in
  let cget = ns_find_ls thclone.th_export ["get"] in
  let cset = ns_find_ls thclone.th_export ["set"] in
  let ct = ns_find_ts thclone.th_export ["t"] in
  let ckey = ns_find_ts thclone.th_export ["key"] in
  let celt = ns_find_ts thclone.th_export ["elt"] in
  let clone_arrays ty (task,tenv) =
    let key,elt =
      match ty.ty_node with
        | Tyapp (_,[key;elt]) -> key,elt
        | _ -> assert false in
    (** create needed alias for the instantiation *)
    let add_ty task ty =
      match ty.ty_node with
        | Tyapp (ts,[]) -> task,ts
        | _ ->
          let ts = create_tysymbol (id_fresh "alias for clone") [] (Some ty) in
          add_ty_decl task [ts,Tabstract],ts in
    let task,tskey = add_ty task key in
    let task,tselt = add_ty task elt in
    let ts_name = "bta_"^(Pp.string_of_wnl Pretty.print_ty ty) in
    let ts = create_tysymbol (id_fresh ts_name) [] None in
    let task = add_ty_decl task [ts,Tabstract] in
    let th_inst = create_inst ~ts:[ct,ts; ckey,tskey; celt,tselt] ~ls:[]
      ~lemma:[] ~goal:[] in
    let task = Task.clone_export task thclone th_inst in
    (** Recover the subtitution *)
    let sls = match task with
      | Some {task_decl = {td_node = Clone(_,{sm_ls=sls})}} -> sls
      | _ -> assert false in
    (** type *)
    (* let tsy = ty_app ts [] in *)
    (** add get to lsymbol *)
    (** Warning its the instanciation, so [elt;key] is really not a
        safe way to define the instancition (depend on variable
        order...) *)
    let add s = Mtyl.add [elt;key] (Mls.find cget sls) s in
    let edefined_lsymbol = Mls.change pget
      (function | None -> Some (add Mtyl.empty) | Some s -> Some (add s))
      tenv.edefined_lsymbol in
    (** add set to lsymbol *)
    let add s = Mtyl.add [elt;key] (Mls.find cset sls) s in
    let edefined_lsymbol = Mls.change pset
      (function | None -> Some (add Mtyl.empty) | Some s -> Some (add s))
      edefined_lsymbol in
    (** add arrays to tsymbol *)
    let add s = Mtyl.add [key;elt] ts s in
    let edefined_tsymbol = Mts.change pt
      (function | None -> Some (add Mtyl.empty) | Some s -> Some (add s))
      tenv.edefined_tsymbol in
    task,{tenv with edefined_lsymbol = edefined_lsymbol;
      edefined_tsymbol = edefined_tsymbol
         } in
  (** add the type which compose keep *)
  let task_tenv = create_env task tenv kept in
  (** add the clone *)
  Sty.fold clone_arrays kept_array task_tenv

let meta_enco_poly = register_meta_excl "enco_poly" [MTstring]

let encoding_smt_array env =
  let th_array = Env.find_theory env ["array"] "Array" in
  Trans.on_used_theory th_array (fun used ->
    if not used then Encoding.encoding_smt env else
      seq [Encoding.monomorphise_goal;
           select_subterm_array th_array;
           Trans.print_meta Encoding.debug Encoding.meta_kept;
           Encoding_instantiate.t (create_env_array env th_array);
           meta_arrays_to_meta_kept;
           Trans.print_meta Encoding.debug Encoding.meta_kept;
           Encoding_bridge.t env;
           Trans.on_flag meta_enco_poly Encoding.ft_enco_poly "decorate" env])

let () = Trans.register_env_transform "encoding_smt_array" encoding_smt_array

(*
Local Variables:
compile-command: "unset LANG; make -j -C ../.. byte"
End:
*)
