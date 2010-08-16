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


open Util
open Ident
open Ty
open Term
open Task
open Theory
open Task
open Decl


let meta_kept = register_meta
  "encoding_instantiate : kept" [MTtysymbol]
let meta_level = register_meta_excl 
  "encoding_instantiate : level" [MTstring]
let meta_complete = register_meta_excl 
  "encoding_instantiate : complete" [MTstring]


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
  | Complete (* The transformation keep the polymorphism *)
  | Incomplete (* The environnement when the transformation isn't complete*)


(* A type is projected on term or type depending 
   of its color (green part,red part, black part) *)
type tty =
  | Tyterm of ty
  | Tyty of ty

let print_tty fmt = function
  | Tyterm ty -> Format.fprintf fmt "(Tyterm %a)" Pretty.print_ty ty
  | Tyty ty -> Format.fprintf fmt "(Tyty %a)" Pretty.print_ty ty

(* It can be backprojected to type, ty_dumb is like a bottom type it
   never appear in final formulas *)
let reduce_to_type = function
  | Tyty ty -> ty
  | Tyterm _ -> ty_dumb


let reduce_to_real = function
  | Tyty ty | Tyterm ty -> ty

(* let reduce_to_pos tenv = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm _ -> match tenv with  *)
(*       | Incomplete -> assert false (\* All is type in this mode *\) *)
(*       | Tenv tenv -> tenv.undeco *)

(* let reduce_to_neg tenv = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm _ -> match tenv with  *)
(*       | Incomplete -> assert false (\* All is type in this mode *\) *)
(*       | Tenv tenv -> tenv.deco *)

(* The environnement of the transformation between two decl (* unmutable *) *)
type env = {
  etenv : tenv;
  ekeep : Sty.t;
  eprojty : ty Mty.t;
  edefined_lsymbol : lsymbol Mtyl.t Mls.t;
  edefined_tsymbol : tysymbol Mtyl.t Mts.t;
}

(* The environnement of the transformation during 
   the transformation of a formula *)
type menv = {
  tenv : tenv;
  keep : Sty.t;
  mutable projty : ty Mty.t;
  mutable defined_lsymbol : lsymbol Mtyl.t Mls.t;
  mutable defined_tsymbol : tysymbol Mtyl.t Mts.t;
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
          Pretty.print_ts)) menv.defined_tsymbol

type tvar = ty Mtv.t

let why_filename = Encoding_decorate.why_filename

let rec projty menv tvar ty =
  let rec aux ty =
    match ty.ty_node with
      | Tyvar _ -> Tyterm ty
      | Tyapp (ts,tyl) ->
        try
          Tyty (Mty.find ty menv.projty)
        with Not_found ->
          match menv.tenv with
            | Incomplete -> 
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
            | Complete ->
              let tyl = List.map aux tyl in
              let tyl_red = List.map reduce_to_type tyl in
              let tys = 
                try
                  Mtyl.find tyl_red (Mts.find ts menv.defined_tsymbol)
                with Not_found ->
                  let insts = try Mts.find ts menv.defined_tsymbol
                    with Not_found -> Mtyl.empty in
                  let args = List.fold_left (fun acc e ->
                    match e with
                      | Tyterm _ -> (create_tvsymbol (id_fresh "a"))::acc
                      | Tyty _ -> acc) [] tyl in
                  let tys = if List.length args = List.length ts.ts_args 
                    then ts 
                    else create_tysymbol (id_clone ts.ts_name) args None in
                  let insts = Mtyl.add tyl_red tys insts in
                  menv.defined_tsymbol <-
                    Mts.add ts insts menv.defined_tsymbol;
                  menv.undef_tsymbol <- Sts.add tys menv.undef_tsymbol;
                  tys in
              let args = List.rev (List.fold_left (fun acc e ->
                match e with
                  | Tyterm ty -> ty::acc
                  | Tyty _ -> acc) [] tyl) in
              Tyterm (ty_app tys args) in
  let ty = ty_inst tvar ty in
  aux ty

let projty_real menv tvar ty = reduce_to_real (projty menv tvar ty)

(* let reduce_to_default menv d = function *)
(*   | Tyty ty -> ty *)
(*   | Tyterm ty -> match menv.tenv with *)
(*       | Incomplete -> ty *)
(*       | Complete -> projty menv Mtv.empty d *)


let reduce_to_default menv tvar d ty = 
  match projty menv tvar ty with
    | Tyty ty -> ty
    | Tyterm _ -> ty_var d

let find_logic menv tvar p tyl ret =
  if ls_equal p ps_equ then p else begin
    let inst = ls_app_inst p tyl ret in
     (*Format.eprintf "inst : %a@."
       (Pp.print_iter2 Mtv.iter Pp.comma Pp.space Pp.nothing 
          Pretty.print_ty) inst;*)
    let inst = Mtv.mapi (reduce_to_default menv tvar) inst in
    let inst_l = Mtv.fold (fun _ v acc -> v::acc) inst [] in
    (* Format.eprintf "p : %a | arg : %a| tyl = %a | inst_l : %i@." *)
    (*   Pretty.print_ls p        *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty) p.ls_args *)
    (*   (Pp.print_list Pp.comma Pretty.print_ty)  *)
    (*   (List.map (fun t -> t.t_ty) tyl) *)
    (*   (List.length inst_l); *)
      try
      let insts = Mls.find p menv.defined_lsymbol in
      Mtyl.find inst_l insts 
    with Not_found ->
      let insts = 
        try
          Mls.find p menv.defined_lsymbol
        with Not_found ->
          Mtyl.empty in
      let proj ty = reduce_to_real (projty menv Mtv.empty ty) in
      let arg = List.map (ty_inst inst) p.ls_args in
      let arg = List.map proj arg in
      let result = option_map (ty_inst inst) p.ls_value in
      let result = option_map proj result in
      let ls = if List.for_all2 ty_equal arg p.ls_args &&
          option_eq ty_equal result p.ls_value 
        then p else create_lsymbol (id_clone p.ls_name) arg result in
      let insts = Mtyl.add inst_l ls insts in
      menv.defined_lsymbol <- Mls.add p insts menv.defined_lsymbol;
      menv.undef_lsymbol <- Sls.add ls menv.undef_lsymbol;
      (* Format.eprintf "fl : env : %a  p : %a | inst : %a@."  *)
      (*   print_env menv *)
      (*   Pretty.print_ls p *)
      (*   (Pp.print_list Pp.comma Pretty.print_ty) inst_l; *)
      ls
  end


(* let deco_res menv t ty = *)
(*   match ty with *)
(*     | Tyty _ -> t *)
(*     | Tyterm tyterm -> *)
(*       match menv.tenv with *)
(*         | Incomplete -> assert false *)
(*         | Tenv tenv -> t_app tenv.sort [tyterm;t] tenv.deco *)

(* let sort_app tenv ty t = *)
(*   match tenv with *)
(*     | Incomplete -> assert false *)
(*     | Tenv tenv -> t_app tenv.sort [ty;t] tenv.deco    *)


let conv_vs menv tvar vsvar vs =
  let ty = projty_real menv tvar vs.vs_ty in
  let vs' = if ty_equal ty vs.vs_ty then vs else
      create_vsymbol (id_clone vs.vs_name) ty in
  Mvs.add vs (t_var vs') vsvar,vs'

(* The convertion of term and formula *)
let rec rewrite_term menv tvar vsvar t = 
  let fnT = rewrite_term menv tvar in
  let fnF = rewrite_fmla menv tvar in
  (* Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t; *)
  match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) -> 
      let tl' = List.map (fnT vsvar) tl in
      let p = find_logic menv tvar p tl (Some t.t_ty) in
      t_app p tl' (projty_real menv tvar t.t_ty)
    | Tif(f, t1, t2) ->
      t_if (fnF vsvar f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2,cb = t_open_bound_cb b in
      let (vsvar',u) = conv_vs menv tvar vsvar u in
      let t1 = fnT vsvar t1 in let t2 = fnT vsvar' t2 in
      t_let t1 (cb u t2)
    | Tcase _ | Teps _ | Tbvar _ ->
      Printer.unsupportedTerm t
        "Encoding instantiate : I can't encode this term"

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
    | _ -> f_map (fnT vsvar) (fnF vsvar) f

(* Generation of all the possible instantiation of a formula *)
let gen_tvar env ts = 
  let aux tv tvarl = 
    let gen tvar ty = Mtv.add tv ty tvar in
    let tvarl' = List.fold_left (fun acc tvar -> 
      Sty.fold (fun ty acc -> gen tvar ty :: acc) env.ekeep acc) [] tvarl in
    match env.etenv with
      | Incomplete -> tvarl'
      | Complete ->
        let gen acc tvar = (Mtv.add tv (ty_var tv) tvar)::acc in
        List.fold_left gen tvarl' tvarl in
  Stv.fold aux ts [Mtv.empty]

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
        (* Format.eprintf "f0 : %a@. env : %a@." Pretty.print_fmla  *)
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


let monomorphise_goal =
  Trans.goal (fun pr f ->
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


let collect_green_part tds =
  (* int and real are always taken in the green part (the constants
     can't be written otherwise). Trigger that only when Int or Real
     theory is used should not be sufficient. *)
  let sts = Sts.add ts_int (Sts.singleton ts_real) in
  let sts = Task.find_tagged_ts meta_kept tds sts in
  let extract ts tys = 
    assert (ts.ts_args = []); (* UnsupportedTySymbol? *)
    Sty.add (match ts.ts_def with
      | None -> ty_app ts []
      | Some ty -> ty) tys in
  let sty = Sts.fold extract sts Sty.empty in
  (* complete by subterm *)
  let rec subty sty ty = ty_fold subty (Sty.add ty sty) ty in
  Sty.fold (flip subty) sty Sty.empty


(* Some general env creation function *) 
let create_env task tenv tds =
  let keep = collect_green_part tds in
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

let create_meta_ty ty acc =
  let name = id_fresh "meta_ty" in
  let ts = create_tysymbol name [] (Some ty) in
  (create_meta meta_kept [MAts ts])::acc

let create_meta_tyl sty d =
  Sty.fold create_meta_ty sty [create_decl d]

let mono_in_goal pr f =
  let sty = (try find_mono ~only_mono:true Sty.empty f
    with Exit -> assert false) (*monomorphise goal should have been used*) in
   create_meta_tyl sty (create_prop_decl Pgoal pr f)

let mono_in_goal = Trans.tgoal mono_in_goal

(* This one use the tag and also all the type in all the definition *)
let mono_in_def d =
  match d.d_node with
    | Dprop (_,_,f) -> let sty = find_mono ~only_mono:false Sty.empty f in
                       create_meta_tyl sty d
    | _ -> [create_decl d]

let mono_in_def = Trans.tdecl mono_in_def None

(* This one use the tag and also all ther type in all the
   monomorphic definition*)
let mono_in_mono d =
  match d.d_node with
    | Dprop (_,_,f) ->
        (try let sty = find_mono ~only_mono:true Sty.empty f in
             create_meta_tyl sty d
         with Exit -> [create_decl d])
    | _ -> [create_decl d]

let mono_in_mono = Trans.tdecl mono_in_mono None


let get_kept =
  Trans.on_meta meta_level (fun tds ->
    match get_meta_exc meta_level tds with
      | None | Some [MAstr "goal"] -> mono_in_goal
      | Some [MAstr "kept"] -> Trans.identity
      | Some [MAstr "all"] -> mono_in_def
      | Some [MAstr "mono"] -> mono_in_mono
      | _ -> failwith "instantiate level wrong argument")


let create_trans_complete metas =
  let tds_kept = Mstr.find meta_kept metas in
  let complete = get_meta_exc meta_complete (Mstr.find meta_complete metas) in
  let task = use_export None builtin_theory in
  let tenv = match complete with
    | None | Some [MAstr "yes"] -> Complete
    | Some [MAstr "no"] ->  Incomplete
    | _ -> failwith "instantiate complete wrong argument" in
  let init_task,env = create_env task tenv tds_kept in
  Trans.fold_map fold_map env init_task

let encoding =
  Trans.compose monomorphise_goal (
    Trans.compose get_kept
      (Trans.on_metas [meta_kept;meta_complete] create_trans_complete))

let () = Trans.register_transform "encoding_instantiate" encoding
