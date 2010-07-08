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

(*
open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl

(* Ce type est utiliser pour indiquer un alpha *)
let tv_dumb = create_tvsymbol (id_fresh "instantiate_alpha") 
let ty_dumb = ty_var tv_dumb

(* TODO : transmettre les tags des logiques polymorphe vers les logiques 
   instantié. Un tag sur un logique polymorphe doit être un tag sur toute 
   la famille de fonctions *) 

module OHTyl = OrderedHashList(Tty)
module Mtyl = Map.Make(OHTyl)

type tenv_aux = {
  deco : ty;
  undeco : ty;
  sort : lsymbol;
  ty : ty;
}

type tenv =
  | Tenv of tenv_aux (* The transformation decorates with tenv_aux.* *)
  | No_black_part (* The environnement when the transformation isn't complete*)

(* A type is projected on term or type depending 
   of its color (green part,red part, black part) *)
type tty =
  | Tyterm of term
  | Tyty of ty

let print_tty fmt = function
  | Tyterm term -> Format.fprintf fmt "(Tyterm %a)" Pretty.print_term term
  | Tyty ty -> Format.fprintf fmt "(Tyty %a)" Pretty.print_ty ty

(* It can be backprojected to type, ty_dumb is like a bottom type it
   never appear in final formulas *)
let reduce_to_type = function
  | Tyty ty -> ty
  | Tyterm _ -> ty_dumb

let reduce_to_pos tenv = function
  | Tyty ty -> ty
  | Tyterm _ -> match tenv with 
      | No_black_part -> assert false (* All is type in this mode *)
      | Tenv tenv -> tenv.undeco

let reduce_to_neg tenv = function
  | Tyty ty -> ty
  | Tyterm _ -> match tenv with 
      | No_black_part -> assert false (* All is type in this mode *)
      | Tenv tenv -> tenv.deco

(* The environnement of the transformation between two decl (* unmutable *) *)
type env = {
  etenv : tenv;
  ekeep : Sty.t;
  eprojty : ty Mty.t;
  edefined_lsymbol : lsymbol Mtyl.t Mls.t;
  edefined_tsymbol : lsymbol Mtyl.t Mts.t;
}

(* The environnement of the transformation during 
   the transformation of a formula *)
type menv = {
  tenv : tenv;
  keep : Sty.t;
  mutable projty : ty Mty.t;
  mutable defined_lsymbol : lsymbol Mtyl.t Mls.t;
  mutable defined_tsymbol : lsymbol Mtyl.t Mts.t;
  mutable undef_lsymbol : Sls.t;
  mutable undef_tsymbol : Sts.t;
}

let print_env fmt menv =
  Format.fprintf fmt "defined_lsymbol (%a)@."
    (Pp.print_iter2 Mls.iter Pp.semi Pp.comma Pretty.print_ls 
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ls)) menv.defined_lsymbol;
  Format.fprintf fmt "defined_tsymbol (%a)@."
    (Pp.print_iter2 Mts.iter Pp.semi Pp.comma Pretty.print_ts 
       (Pp.print_iter2 Mtyl.iter Pp.semi Pp.arrow
          (Pp.print_list Pp.space Pretty.print_ty)
          Pretty.print_ls)) menv.defined_tsymbol

type tvar = {
  tvar_term : vsymbol Mtv.t;
  tvar_ty : ty Mtv.t;
}

let why_filename = Encoding_decorate.why_filename
(* Useful function *)
let rec logic_inst tl = function
  | None -> List.map reduce_to_type tl
  | Some ty -> (reduce_to_type ty) :: (logic_inst tl None)

let find_logic menv p tyl ty =
  if ls_equal p ps_equ then p else
  let inst = logic_inst tyl ty in
  (*Format.eprintf "fl : env : %a  p : %a | inst : %a@." 
    print_env menv
    Pretty.print_ls p
    (Pp.print_list Pp.comma Pretty.print_ty) inst;*)
  try
    let insts = Mls.find p menv.defined_lsymbol in
    Mtyl.find inst insts 
  with Not_found ->
    let insts = 
      try
        Mls.find p menv.defined_lsymbol
      with Not_found ->
        Mtyl.empty in
    let arg = List.map (reduce_to_neg menv.tenv) tyl in
    let result = option_map (reduce_to_pos menv.tenv) ty in
    let ls = if List.for_all2 ty_equal arg p.ls_args &&
        option_eq ty_equal result p.ls_value 
      then p else create_lsymbol (id_clone p.ls_name) arg result in
    let insts = Mtyl.add inst ls insts in
    menv.defined_lsymbol <- Mls.add p insts menv.defined_lsymbol;
    menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol;
    ls

let rec projty menv tvar ty : tty =
  let rec aux ty =
    match ty.ty_node with
      | Tyvar tv -> Tyterm (t_var (Mtv.find tv tvar.tvar_term))
      | Tyapp (ts,tyl) ->
        try
          Tyty (Mty.find ty menv.projty)
        with Not_found ->
          match menv.tenv with
            | No_black_part -> 
              (* In this configuration there is no term representing type,
                 all type are a type or are in the black part 
                 (the or is not a xor)*)
              let preid = id_clone ts.ts_name in
              let ts = create_tysymbol preid [] None (*Some ty*) in
              let tty = ty_app ts [] in
              menv.projty <- Mty.add ty tty menv.projty;
              menv.undef_tsymbol <- Sts.add ts menv.undef_tsymbol;
              (*Format.eprintf "projty : ts : %a env : %a@." Pretty.print_ts ts
              print_env menv;*)
              Tyty tty
            | Tenv tenv ->
              let tyl = List.map aux tyl in
              let tyl_red = List.map reduce_to_type tyl in
              let ls = 
                try
                  Mtyl.find tyl_red (Mts.find ts menv.defined_tsymbol)
                with Not_found ->
                  let insts = try Mts.find ts menv.defined_tsymbol
                    with Not_found -> Mtyl.empty in
                  let args = List.fold_left (fun acc e ->
                    match e with
                      | Tyterm _ -> tenv.ty::acc
                      | Tyty _ -> acc) [] tyl in
                  let ls = create_fsymbol (id_clone ts.ts_name) args tenv.ty in
                  let insts = Mtyl.add tyl_red ls insts in
                  menv.defined_tsymbol <-
                    Mts.add ts insts menv.defined_tsymbol;
                  menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol;
                  ls in
              let args = List.rev (List.fold_left (fun acc e ->
                match e with
                  | Tyterm t -> t::acc
                  | Tyty _ -> acc) [] tyl) in
              Tyterm (t_app ls args tenv.ty) in
  let ty = ty_inst tvar.tvar_ty ty in
  aux ty

let deco_res menv t ty =
  match ty with
    | Tyty _ -> t
    | Tyterm tyterm ->
      match menv.tenv with
        | No_black_part -> assert false
        | Tenv tenv -> t_app tenv.sort [tyterm;t] tenv.deco

let sort_app tenv ty t =
  match tenv with
    | No_black_part -> assert false
    | Tenv tenv -> t_app tenv.sort [ty;t] tenv.deco   


let conv_vs menv tvar vsvar vs =
  let ty = projty menv tvar vs.vs_ty in
  let vs'= create_vsymbol (id_clone vs.vs_name) (reduce_to_pos menv.tenv ty) in
  (match ty with
    | Tyterm t -> Mvs.add vs (sort_app menv.tenv t (t_var vs')) vsvar
    | Tyty _ -> Mvs.add vs (t_var vs') vsvar),vs'

let conv_vs_let menv tvar vsvar vs =
  let ty = projty menv tvar vs.vs_ty in
  let vs'= create_vsymbol (id_clone vs.vs_name) (reduce_to_neg menv.tenv ty) in
  (match ty with
    | Tyterm _ -> Mvs.add vs (t_var vs') vsvar
    | Tyty _ -> Mvs.add vs (t_var vs') vsvar),vs'

(* The convertion of term and formula *)
let rec rewrite_term menv tvar vsvar t = 
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) -> 
      let tl' = List.map (fnT vsvar) tl in
      let tyl = List.map (fun t -> projty menv tvar t.t_ty) tl in
      let ty = projty menv tvar t.t_ty in
      let p = find_logic menv p tyl (Some ty) in
      let app = t_app_infer p tl' in
      deco_res menv app ty
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2 = t_open_bound b in
      let (vsvar',u) = conv_vs_let menv tvar vsvar u in
      let t1' = fnT vsvar t1 in let t2' = fnT vsvar' t2 in
      if t_equal t1' t1 && t_equal t2' t2 then t else t_let u t1' t2'
    | Tcase _ | Teps _ | Tbvar _ ->
      Register.unsupportedTerm t
        "Encoding instantiate : I can't encode this term"

and rewrite_fmla menv tvar vsvar f = 
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  match f.f_node with
    | Fapp(p, tl) ->
      let tl' = List.map (fnT vsvar) tl in
      let tyl = List.map (fun t -> projty menv tvar t.t_ty) tl in
      let p = find_logic menv p tyl None in
      f_app p tl'
    | Fquant(q, b) -> 
      let vl, tl, f1 = f_open_quant b in
      let vsvar,vl = map_fold_left (conv_vs menv tvar) vsvar vl in
      
      let f1' = fnF vsvar f1 in 
      (* Ici un trigger qui ne match pas assez de variables 
         peut être généré *)
      let tl = tr_map (fnT vsvar) (fnF vsvar) tl in
        (*if f_equal f1' f1 &&  vsvar' == vsvar (*&& tr_equal tl' tl*) then f
        else *)
          let vl = List.rev vl in
          f_quant q vl tl f1'
    | Flet (t1, b) -> let u,f2 = f_open_bound b in
      let (vsvar',u) = conv_vs_let menv tvar vsvar u in
      let t1' = fnT vsvar t1 in let f2' = fnF vsvar' f2 in
      assert (u.vs_ty == t1'.t_ty);
      (*if t_equal t1' t1 && f_equal f2' f2 then f else *)
        f_let u t1' f2'
    | _ -> f_map (fnT vsvar) (fnF vsvar) f

(* Generation of all the possible instantiation of a formula *)
let gen_tvar env ts = 
  let aux tv tvarl = 
    let gen tvar ty = {tvar with tvar_ty = Mtv.add tv ty tvar.tvar_ty} in
    let tvarl' = List.fold_left (fun acc tvar -> 
      Sty.fold (fun ty acc -> gen tvar ty :: acc) env.ekeep acc) [] tvarl in
    match env.etenv with
      | No_black_part -> tvarl'
      | Tenv tenv ->
        let gen acc tvar =
          let vs = create_vsymbol (id_clone (tv.tv_name)) tenv.ty in
          {tvar with tvar_term = Mtv.add tv vs tvar.tvar_term}::acc in
        List.fold_left gen tvarl' tvarl in
  Stv.fold aux ts [{tvar_term = Mtv.empty; tvar_ty = Mtv.empty}]

(*
let ty_args_from_tty = 
  List.fold_left (fun acc e ->
    match e with
      | Tyterm _ -> tenv.ty::acc
      | Tyty _ -> acc) [] 

let conv_to_tty env ts tyl proj_ty =
  let ty = ty_app ts tyl in
  if Sty.mem ty env.keep 
  then (assert (Mty.mem ty proj_ty); proj_ty)
  else let args = ty_args_from_tty tyl in
*)


(* Free type in terms and formulae *)
let rec t_fold_ty fty s t =
  let s = t_fold (t_fold_ty fty) (f_fold_ty fty) s t in
  let s = fty s t.t_ty in
  match t.t_node with
    | Teps fb -> 
      let vs,_ = f_open_bound fb in
      fty s vs.vs_ty
    | _ -> s
and f_fold_ty fty s f =
  let s = f_fold (t_fold_ty fty) (f_fold_ty fty) s f in
  match f.f_node with
    | Fquant (_,fq) ->
      let (vsl,_,_) = f_open_quant fq in
      List.fold_left (fun s vs -> fty s vs.vs_ty) s vsl
    | _ -> s

let ty_quant =
  let rec add_vs s ty = match ty.ty_node with
    | Tyvar vs -> Stv.add vs s
    | _ -> ty_fold add_vs s ty in
  f_fold_ty add_vs Stv.empty

(* The Core of the transformation *)
let fold_map task_hd ((env:env),task) =
  match task_hd.task_decl.td_node with
    | Use _ | Clone _ | Meta _ -> env,add_tdecl task task_hd.task_decl
    | Decl d -> match d.d_node with
    | Dtype [_,Tabstract] -> (env,task)
    (* Nothing here since the type kept are already defined and the other 
       will be lazily defined *)
    | Dtype _ -> Register.unsupportedDecl 
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | Dlogic l ->
        let fn = function
          | _, Some _ -> 
              Register.unsupportedDecl 
                d "encoding_decorate : I can't encode definition. \
Perhaps you could use eliminate_definition"
          | _, None -> () in
            (* Noting here since the logics are lazily defined *)
            List.iter fn l; (env,task)
    | Dind _ -> Register.unsupportedDecl
        d "encoding_decorate : I can't work on inductive"
        (* let fn (pr,f) = pr, fnF f in *)
        (* let fn (ps,l) = ps, List.map fn l in *)
        (* [create_ind_decl (List.map fn l)] *)
    | Dprop (k,pr,f) ->
      let tvl = ty_quant f in
      let tvarl = gen_tvar env tvl in
      let tvarl_len = List.length tvarl in
      let menv =  {
        tenv = env.etenv;
        keep = env.ekeep;
        projty = env.eprojty;
        defined_lsymbol = env.edefined_lsymbol;
        defined_tsymbol = env.edefined_tsymbol;
        undef_lsymbol = Sls.empty;
        undef_tsymbol = Sts.empty;
      } in
      let conv_f task tvar = 
        let f = rewrite_fmla menv tvar Mvs.empty f in
        (*Format.eprintf "f : %a env : %a@." Pretty.print_fmla f
          print_env menv;*)
        let tvl = Mtv.fold (fun _ vs acc -> vs::acc) tvar.tvar_term [] in
        let f = f_forall tvl [] f in
        let pr = 
          if tvarl_len = 1 then pr 
          else create_prsymbol (id_clone pr.pr_name) in
        (*Format.eprintf "undef ls : %a, ts : %a@."
          (Pp.print_iter1 Sls.iter Pp.comma Pretty.print_ls) menv.undef_lsymbol
          (Pp.print_iter1 Sts.iter Pp.comma Pretty.print_ts)
          menv.undef_tsymbol;*)
        let task = Sts.fold 
          (fun ts task -> add_ty_decl task [ts,Tabstract]) 
          menv.undef_tsymbol task in
        let task = Sls.fold 
          (fun ls task -> add_logic_decl task [ls,None]) 
          menv.undef_lsymbol task in
        let task = add_prop_decl task k pr f in
        task
      in
      {env with edefined_lsymbol = menv.defined_lsymbol;
        edefined_tsymbol = menv.defined_tsymbol;
        eprojty = menv.projty;
      },
      List.fold_left conv_f task tvarl

(* A Pre-transformation to work on monomorphic goal *)
let on_goal fn =
  let fn task = match task with
    | Some {Task.task_decl = { td_node =
          Decl ({d_node = Decl.Dprop (Pgoal,pr,fmla)})};
           task_prev = task_prev} -> 
        (List.fold_left Task.add_decl) task_prev (fn pr fmla)
    | _ -> assert false in
  Trans.store fn

let monomorphise_goal =
  on_goal (fun pr f ->
    let stv = ty_quant f in
    let mty,ltv = Stv.fold (fun tv (mty,ltv) -> 
      let ts = create_tysymbol (id_clone tv.tv_name) [] None in
      Mtv.add tv (ty_app ts []) mty,ts::ltv) stv (Mtv.empty,[]) in
    let f = f_ty_subst mty Mvs.empty f in
    let acc = [create_prop_decl Pgoal pr f] in
    let acc = List.fold_left
      (fun acc ts -> (create_ty_decl [ts,Tabstract]) :: acc)
      acc ltv in
    acc)

let monomorphise_goal = Trans.store (fun () -> monomorphise_goal)

(* The prelude for the complete transformation *)
let load_prelude env =
  let prelude = Env.find_theory env why_filename "Prelude" in
  let sort = Theory.ns_find_ls prelude.th_export ["sort"] in
  let ty = ty_app (Theory.ns_find_ts prelude.th_export ["ty"]) [] in
  let deco = ty_app (Theory.ns_find_ts prelude.th_export ["deco"]) [] in
  let undeco = ty_app (Theory.ns_find_ts prelude.th_export ["undeco"]) [] in
  let task = None in
  let task = Task.use_export task prelude in
  task,{ deco = deco;
    undeco = undeco;
    sort = sort;
    ty = ty}

(* Some general env creation function *) 
let create_env task tenv sty =
  let keep = sty in
  let projty = Sty.fold (fun ty ty_ty -> 
    let ty2 = match ty.ty_node with 
      | Tyapp (_,[]) -> ty
      | Tyapp (ts,_) -> 
        let ts = create_tysymbol (id_clone ts.ts_name) [] None in 
        ty_app ts []
      | _ -> assert false in
    Mty.add ty ty2 ty_ty)
    keep Mty.empty in
  let task = Mty.fold (fun _ ty task -> 
    match ty.ty_node with
      | Tyapp (ts,[]) -> add_ty_decl task [ts,Tabstract]
      | _ -> assert false) projty task in
    task,{
    etenv = tenv;
    ekeep = keep;
    eprojty = projty;
    edefined_lsymbol = Mls.empty;
    edefined_tsymbol = Mts.empty
  }


let create_env_complete env sty =
  let task,tenv = load_prelude env in
  create_env task (Tenv tenv) sty

let create_env_nbp sty =
  let task = use_export None builtin_theory in
  let tenv = No_black_part in
  create_env task tenv sty

let register_transform name create_env =
  let t = Trans.store_query
    (fun query ->
       Trans.store 
         (fun task ->
            let task = Register.apply monomorphise_goal task in
            let drv = Driver.query_driver query in
            let env = Driver.query_env query in
            let init_task,env = create_env env drv task in
            Trans.apply (Trans.fold_map fold_map env init_task) task)) in
  Trans.register_transform name t

(* The most simple configuration takes only the tag keep into account *)
let is_kept query ts = 
  ts.ts_args = [] &&  
    begin
      ts_equal ts ts_int || ts_equal ts ts_real  (* for the constant *)
      || let tags = Driver.query_tags query ts.ts_name in
         Sstr.mem Encoding_decorate.kept_tag tags
    end

let fold_decl f = 
  Trans.fold (fun task_hd acc ->
    match task_hd.task_decl.td_node with
      | Use _ | Clone _ | Meta _ -> acc
      | Decl d -> f d acc)

let look_for_keep query d sty =
  match d.d_node with
    | Dtype [ts,Tabstract] -> 
        if is_kept query ts then Sty.add (ty_app ts []) sty else sty
    | Dtype _ -> Register.unsupportedDecl 
        d "encoding_decorate : I can work only on abstract\
            type which are not in recursive bloc."
    | _ -> sty

let look_for_keep =
  Trans.store_query
    (fun query -> fold_decl (look_for_keep query) Sty.empty)

let () = register_transform "encoding_instantiate"
  (fun env drv task -> 
     let sty = Register.apply_driver look_for_keep drv task in
     create_env_complete env sty)

let () = register_transform "encoding_instantiate_nbp"
  (fun _ drv task -> 
     let sty = Register.apply_driver look_for_keep drv task in
     create_env_nbp sty)

(* This one take use the tag but also all the type which appear in the goal *)
let is_ty_mono ~only_mono ty = 
  try
    let rec check () ty = match ty.ty_node with
      | Tyvar _ -> raise Exit
      | Tyapp _ -> ty_fold check () ty in
    check () ty;
    true
  with Exit when not only_mono -> false

let find_mono ~only_mono sty f = 
  let add sty ty = if is_ty_mono ~only_mono ty then Sty.add ty sty else sty in
  f_fold_ty add sty f

let mono_in_goal d sty =
  match d.d_node with
    | Dprop (Pgoal,_,f) -> 
        (try find_mono ~only_mono:true sty f
         with Exit -> assert false) (*monomorphise goal should have been used*)
    | _ -> sty

let mono_in_goal =
  Trans.store (fun () -> fold_decl mono_in_goal Sty.empty)

let () = register_transform "encoding_instantiate_goal"
  (fun env drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_goal task in
     create_env_complete env (Sty.union sty1 sty2))

let () = register_transform "encoding_instantiate_goal_nbp"
  (fun _ drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_goal task in
     create_env_nbp (Sty.union sty1 sty2))

(* This one use the tag and also all the type in all the definition *)
let mono_in_def d sty =
  match d.d_node with
    | Dprop (_,_,f) -> find_mono ~only_mono:false sty f
    | _ -> sty

let mono_in_def =
  Trans.store (fun () -> fold_decl mono_in_def Sty.empty)

let () = register_transform "encoding_instantiate_def"
  (fun env drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_def task in
     create_env_complete env (Sty.union sty1 sty2))

let () = register_transform "encoding_instantiate_def_nbp"
  (fun _ drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_def task in
     create_env_nbp (Sty.union sty1 sty2))

(* This one use the tag and also all ther type in all the 
   monomorphic definition*)
let mono_in_mono d sty =
  match d.d_node with
    | Dprop (_,_,f) -> 
        (try find_mono ~only_mono:true sty f
         with Exit -> sty)
    | _ -> sty

let mono_in_mono =
  Trans.store (fun () -> fold_decl mono_in_mono Sty.empty)

let () = register_transform "encoding_instantiate_mono"
  (fun env drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_mono task in
     create_env_complete env (Sty.union sty1 sty2))

let () = register_transform "encoding_instantiate_mono_nbp"
  (fun _ drv task -> 
     let sty1 = Register.apply_driver look_for_keep drv task in
     let sty2 = Register.apply mono_in_mono task in
     create_env_nbp (Sty.union sty1 sty2))

*)
