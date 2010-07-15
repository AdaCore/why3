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

let why_filename = Encoding_decorate.why_filename

let meta_enum = Eliminate_algebraic.meta_enum
  
type tenv = {kept  : Sts.t;
             projs : lsymbol Hts.t} 
    (* trans_lsymbol ne depend pour l'instant pas du but, 
       comme specials_type ne depend pas*)
    

let load_prelude _env =
  let task = None in
  let projs = Hts.create 17 in
  task, projs

let add_proj tenv ts =
  let name = ts.ts_name.id_string in
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let proj = create_fsymbol (id_fresh ("proj"^name)) [ty]  ty in
  Hts.add tenv.projs ts proj;
  proj

let find_proj tenv ty =
  match ty.ty_node with
    | Tyapp (ts,_) when Sts.mem ts tenv.kept -> Some (Hts.find tenv.projs ts)
    | _ -> None
  

let proj_if_needed tenv t =
  match find_proj tenv t.t_ty with
    | None -> t
    | Some p -> t_app p [t] t.t_ty

let conv_vs tenv (vsvar,acc) vs =
  let tres,vsres =
    let t = t_var vs in
    proj_if_needed tenv t,vs in
  (Mvs.add vs tres vsvar,vsres::acc)

let rec rewrite_term tenv vsvar t =
  (*Format.eprintf "@[<hov 2>Term : %a =>@\n@?" Pretty.print_term t;*)
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv vsvar in
  match t.t_node with
    | Tconst _ -> t
    | Tvar x -> Mvs.find x vsvar
    | Tapp(p,tl) ->
        let tl = List.map (fnT vsvar) tl in
        proj_if_needed tenv (t_app p tl t.t_ty)
    | Tif (f, t1, t2) -> 
        t_if (fnF f) (fnT vsvar t1) (fnT vsvar t2)
    | Tlet (t1, b) -> let u,t2 = t_open_bound b in
      let t1' = fnT vsvar t1 in let t2' = fnT vsvar t2 in
      if t_equal t1' t1 && t_equal t2' t2 then t else t_let u t1' t2'
    | Tcase _ | Teps _ | Tbvar _ ->
        Printer.unsupportedTerm t
          "Encoding decorate : I can't encode this term"

and rewrite_fmla tenv vsvar f =
(*  Format.eprintf "@[<hov 2>Fmla : %a =>@\n@?" Pretty.print_fmla f;*)
  let fnT = rewrite_term tenv vsvar in
  let fnF = rewrite_fmla tenv in
  match f.f_node with
    | Fapp(p, tl) -> 
        let tl = List.map fnT tl in
        f_app p tl
    | Fquant (q, b) -> let vl, tl, f1 = f_open_quant b in
      let (vsvar',vl) = List.fold_left (conv_vs tenv) (vsvar,[]) vl in
      let f1' = fnF vsvar' f1 in 
      (* Ici un trigger qui ne match pas assez de variables 
         peut être généré *)
      let tl = tr_map (rewrite_term tenv vsvar') (fnF vsvar') tl in
        (*if f_equal f1' f1 &&  vsvar' == vsvar (*&& tr_equal tl' tl*) then f
        else *)
          let vl = List.rev vl in
          f_quant q vl tl f1'
    | Flet (t1, b) -> let u,f2 = f_open_bound b in
      let t1' = fnT t1 in let f2' = fnF vsvar f2 in
      (*if t_equal t1' t1 && f_equal f2' f2 then f else *)
       f_let u t1' f2'
    | _ -> f_map fnT (fnF vsvar) f

let decl (tenv:tenv) d =
  let fnT = rewrite_term tenv Mvs.empty in
  let fnF = rewrite_fmla tenv Mvs.empty in
  match d.d_node with
    | Dtype [ts,Tabstract] when Sts.mem ts tenv.kept -> 
      let ls = add_proj tenv ts in
      [d;create_logic_decl [(ls,None)]]
    | Dtype [_] -> [d]
    (* Can be loosen *)
    | Dtype _ -> Printer.unsupportedDecl d
      "encoding_decorate : I can work only on abstract \
        type which are not in recursive bloc."
    | _ -> [decl_map fnT fnF d] (* TODO treat parameters *)


(*
let decl tenv d =
  Format.eprintf "@[<hov 2>Decl : %a =>@\n@?" Pretty.print_decl d;
  let res = decl tenv d in
  Format.eprintf "%a@]@." (Pp.print_list Pp.newline Pretty.print_task_tdecl)
    res;
  res
*)

let t env = 
  let init_task, projs = load_prelude env in
  Trans.on_meta meta_enum (fun tds ->
    let kept = Task.find_tagged_ts meta_enum tds Sts.empty in
    let tenv = { kept = kept; projs = projs} in
    Trans.decl (decl tenv) init_task)

let () = Trans.register_env_transform "encoding_enumeration" t
