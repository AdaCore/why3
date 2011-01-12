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
type env = {
  keep : ty Mty.t;
  poly_ts : tysymbol;
  edefined_lsymbol : lsymbol Mtyl.t Mls.t;
}

(* The environnement of the transformation during
   the transformation of a formula *)
type menv = {
  env : env;
  mutable defined_lsymbol : lsymbol Mtyl.t Mls.t;
  mutable undef_lsymbol : Sls.t;
}

let print_env fmt menv =
  Format.fprintf fmt "defined_lsymbol (%a)@."
    (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ls)) menv.defined_lsymbol

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

let projty menv ty = Mty.find_default ty ty menv.env.keep

let conv_vs menv tvar vsvar vs =
  let ty = projty menv (ty_inst tvar vs.vs_ty) in
  let vs' = if ty_equal ty vs.vs_ty then vs else
      create_vsymbol (id_clone vs.vs_name) ty in
  Mvs.add vs (t_var vs') vsvar,vs'


(* Weakmemo only on the symbols *)
let clone_lsymbol p arg result = create_lsymbol (id_clone p.ls_name) arg result

let find_logic menv tvar p tl tyv =
  if ls_equal p ps_equ then p else begin
    (** project the type on : keep + {dumb} *)
    let to_dumb {t_ty = ty} =
      let ty = ty_inst tvar ty in
      Mty.find_default ty ty_dumb menv.env.keep in
    let inst_l = List.map to_dumb tl in
    let inst_tyv = option_map to_dumb tyv in
    let inst_l_tyv = option_apply inst_l (fun e -> e::inst_l) inst_tyv in
    (* Format.eprintf "env : %ap : %a | arg : %a| tyl = %a | inst_l : %a@." *)
    (*   print_env menv *)
    (*   Pretty.print_ls p *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) p.ls_args *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) *)
    (*   (List.map (fun t -> ty_inst tvar t.t_ty) tl) *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) inst_l_tyv; *)
    try
      let insts = Mls.find p menv.defined_lsymbol in
      Mtyl.find inst_l_tyv insts
    with Not_found ->
      let insts = Mls.find_default p Mtyl.empty menv.defined_lsymbol in
      let to_new tyd ty = if ty_equal tyd ty_dumb then ty else tyd in
      let arg = List.map2 to_new inst_l p.ls_args in
      let value = option_map2 to_new inst_tyv p.ls_value in
      let ls = if List.for_all2 ty_equal arg p.ls_args &&
          option_eq ty_equal value p.ls_value
        then p else clone_lsymbol p arg value in
      let insts = Mtyl.add inst_l_tyv ls insts in
      menv.defined_lsymbol <- Mls.add p insts menv.defined_lsymbol;
      menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol;
      ls
  end

(* The convertion of term and formula *)
let rec rewrite_term menv tvar vsvar t =
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  (* Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t; *)
  let t = match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
      let tl' = List.map (fnT vsvar) tl in
      let p = find_logic menv tvar p tl (Some t) in
      t_app p tl' (projty menv (ty_inst tvar t.t_ty))
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs menv tvar vsvar u in
      let t1 = fnT vsvar t1 in let t2 = fnT vsvar' t2 in
      t_let t1 (cb u t2)
    | Tcase _ | Teps _ ->
      Printer.unsupportedTerm t
        "Encoding instantiate : I can't encode this term" in
  (* Format.eprintf "@[<hov 2>Term : => %a : %a@\n@?" *)
  (*   Pretty.print_term t Pretty.print_ty t.t_ty; *)
  t

and rewrite_fmla menv tvar vsvar f =
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  (* Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f; *)
  match f.f_node with
    | Fapp(p, tl) ->
      let tl' = List.map (fnT vsvar) tl in
      let p = find_logic menv tvar p tl None in
      f_app p tl'
    | Fquant(q, b) ->
      let vl, tl, f1, cb = f_open_quant_cb b in
      let vsvar,vl = map_fold_left (conv_vs menv tvar) vsvar vl in

      let f1 = fnF vsvar f1 in
      (* Ici un trigger qui ne match pas assez de variables
         peut être généré *)
      let tl = tr_map (fnT vsvar) (fnF vsvar) tl in
      let vl = List.rev vl in
      f_quant q (cb vl tl f1)
    | Flet (t1, b) -> let u,f2,cb = f_open_bound_cb b in
      let (vsvar',u) = conv_vs menv tvar vsvar u in
      let t1 = fnT vsvar t1 and f2 = fnF vsvar' f2 in
      (* Format.eprintf "u.vs_ty : %a == t1.t_ty : %a@." *)
      (*    Pretty.print_ty u.vs_ty Pretty.print_ty t1.t_ty; *)
      assert (u.vs_ty == t1.t_ty);
      f_let t1 (cb u f2)
    | _ -> f_map (fun _ -> assert false) (fnF vsvar) f


module Ssubst =
  Set.Make(struct type t = ty Mtv.t
                  let compare = Mtv.compare OHTy.compare end)


(* Generation of all the possible instantiation of a formula *)
let gen_tvar su =
  (* Try to apply one subst on all the other subst generated until then
     (ie. in su), that give newly generated subst (ie to put in su)*)
  let aux subst su =
    (* filter the possible application of substitution *)
    let disj_union m1 m2 = Mtv.union (fun _ ty1 ty2 ->
      if ty_equal ty1 ty2 then Some ty1 else raise Exit) m1 m2 in
    let fold subst1 acc =
      try Ssubst.add (disj_union subst1 subst) acc with Exit -> acc in
    Ssubst.fold fold su su in
  Ssubst.fold aux su (Ssubst.singleton (Mtv.empty))

(* find all the possible instantiation which can give a type of env.keep *)
let ty_quant env =
  let rec add_vs s ty =
    let s = ty_fold add_vs s ty in
    match ty.ty_node with
      | Tyapp(app,_) when ts_equal app env.poly_ts  ->
        Mty.fold (fun uty _ s ->
          try
            Ssubst.add (ty_match Mtv.empty ty uty) s
          with Ty.TypeMismatch _ ->
            (* No instantiation possible *)
            s
        )
          env.keep s
      | _ -> s in
  f_ty_fold add_vs Ssubst.empty

(* The Core of the transformation *)
let fold_map task_hd ((env:env),task) =
  match task_hd.task_decl.td_node with
    | Use _ | Clone _ | Meta _ -> env,add_tdecl task task_hd.task_decl
    | Decl d -> match d.d_node with
    | Dtype [_,Tabstract] -> env,add_tdecl task task_hd.task_decl
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
            (* Noting here since the logics are lazily defined *)
            List.iter fn l; (env,task)
    | Dind _ -> Printer.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
      let tvl = ty_quant env f in
      let tvarl = gen_tvar tvl in
      let tvarl_len = Ssubst.cardinal tvarl in
      let menv =  {
        env = env;
        defined_lsymbol = env.edefined_lsymbol;
        undef_lsymbol = Sls.empty;
      } in
      let conv_f tvar task =
        (* Format.eprintf "f0 : %a@. env : %a@." Pretty.print_fmla *)
        (*   (f_ty_subst tvar Mvs.empty f) *)
        (*   print_env menv; *)
        let f = rewrite_fmla menv tvar Mvs.empty f in
        (* Format.eprintf "f : %a@. env : %a@." Pretty.print_fmla f *)
        (*   print_env menv; *)
        let pr =
          if tvarl_len = 1 then pr
          else create_prsymbol (id_clone pr.pr_name) in
        (* Format.eprintf "undef ls : %a, ts : %a@." *)
        (*   (Pp.print_iter1 Sls.iter Pp.comma Pretty.print_ls) *)
        (*   menv.undef_lsymbol *)
        (*   (Pp.print_iter1 Sts.iter Pp.comma Pretty.print_ts) *)
        (*   menv.undef_tsymbol; *)
        let task = Sls.fold
          (fun ls task -> add_logic_decl task [ls,None])
          menv.undef_lsymbol task in
        let task = add_prop_decl task k pr f in
        task
      in
      let task = Ssubst.fold conv_f tvarl task in
      {env with edefined_lsymbol = menv.defined_lsymbol}, task

let ty_all_quant =
  let rec add_vs s ty = match ty.ty_node with
    | Tyvar vs -> Stv.add vs s
    | _ -> ty_fold add_vs s ty in
  f_ty_fold add_vs Stv.empty

let monomorphise_goal =
  Trans.goal (fun pr f ->
    let stv = ty_all_quant f in
    let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
      let ts = create_tysymbol (id_clone tv.tv_name) [] None in
      Mtv.add tv (ty_app ts []) mty,ts::ltv) stv (Mtv.empty,[]) in
    let f = f_ty_subst mty Mvs.empty f in
    let acc = [create_prop_decl Pgoal pr f] in
    let acc = List.fold_left
      (fun acc ts -> (create_ty_decl [ts,Tabstract]) :: acc)
      acc ltv in
    acc)

let meta_kept_array = register_meta "encoding : kept_array" [MTtysymbol]

let collect_arrays poly_ts tds =
  let extract ts tys =
    assert (ts.ts_args = []); (* UnsupportedTySymbol : TODO *)
    Mty.add (match ts.ts_def with
      | None -> Printer.unsupportedType (ty_app ts [])
        "Encoding_arrays : apply only on alias for array"
      | Some ({ty_node = Tyapp (app,_)} as ty)
          when not (ts_equal app poly_ts) ->
        Printer.unsupportedType ty "Encoding_arrays : apply only on array"
      | Some ty -> ty)
      ts tys in
  Sts.fold extract tds Mty.empty

let meta_mono_array = register_meta "encoding_arrays : mono_arrays"
  [MTtysymbol;MTty;MTty]

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

(* This one take use the tag but also all the type which appear in the goal *)
let is_ty_mono ~only_mono ty =
  try
    let rec check () ty = match ty.ty_node with
      | Tyvar _ -> raise Exit
      | Tyapp _ -> ty_fold check () ty in
    check () ty;
    true
  with Exit when not only_mono -> false


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


(*
Local Variables:
compile-command: "unset LANG; make -j -C ../.. byte"
End:
*)
