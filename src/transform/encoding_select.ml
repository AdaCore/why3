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
open Libencoding

let is_ty_mono ty =
  try
    let rec check () ty = match ty.ty_node with
      | Tyvar _ -> raise Exit
      | Tyapp _ -> ty_fold check () ty in
    check () ty;
    true
  with Exit -> false


let good_for_env ls =
  let tyl = option_apply ls.ls_args (fun e -> e::ls.ls_args) ls.ls_value in
  let good ty =
    match ty.ty_node with
      | Tyvar _ -> false
      | _ -> not (Stv.is_empty (ty_freevars Stv.empty ty))
  in
  List.exists good tyl 

module Lskept = struct
  type lskept = Sls.t

  (** Hunting lskept... *)
  let add_mono_lskept lskept ls _ _ =
    if good_for_env ls then Sls.add ls lskept else lskept

  let fold_add_lskept task lskept = match task.task_decl.td_node with
    | Decl { d_node = Dlogic l } ->
      let accum lskept (ls,_) = add_mono_lskept lskept ls () () in
      List.fold_left accum lskept l
    | _ -> lskept

  let metas_of_lskept sls decls =
    let create_meta_ls ls = create_meta meta_lskept [MAls ls] in
      Sls.fold (flip $ cons create_meta_ls) sls decls

end

module Kept = struct
  type kept = Sty.t

  let add_mono_kept kept _ tyl tyv =
    if List.for_all is_ty_mono tyl && option_apply true is_ty_mono tyv then
      let tydisl = option_apply tyl (fun e -> e::tyl) tyv in
      List.fold_left (fun acc ty -> Sty.add ty acc) kept tydisl
    else kept

  let fold_add_kept task kept = match task.task_decl.td_node with
    | Decl { d_node = Dprop (_,_,f)} -> t_app_fold add_mono_kept kept f
    | _ -> kept

  let metas_of_kept sty decls =
    let create_meta_ty ty = create_meta meta_kept [MAty ty] in
      Sty.fold (flip $ cons create_meta_ty) sty decls

end

module Env = struct
  include Encoding_distinction.Env

(** creation functions *)
(** find type in env *)
  let meta_kept_from_env decls env =
    let fold_ls _ insts decls =
      let fold_inst inst _ decls =
        let fold_ty decls ty =
          create_meta meta_kept [MAty ty] :: decls in
        List.fold_left fold_ty decls inst
      in
      Mtyl.fold fold_inst insts decls
    in
    Mls.fold fold_ls env decls


(** Using an lskept *)
  let env_from_fold lskept (env,kept) ls tyl tyv =
    if Sls.mem ls lskept &&
      List.for_all is_ty_mono tyl && option_apply true is_ty_mono tyv then
      let tydisl = option_apply tyl (fun e -> e::tyl) tyv
      in
      let lsinst = create_lsymbol (id_clone ls.ls_name) tyl tyv in
      let insts = Mls.find_default ls Mtyl.empty env in
      Mls.add ls (Mtyl.add tydisl lsinst insts) env,
      List.fold_left (fun acc ty -> Sty.add ty acc) kept tydisl
    else (env,kept)

(** Without discrimination *)
  let add_mono_instantiation env ls tyl tyv =
    if List.for_all is_ty_mono tyl && option_apply true is_ty_mono tyv
      && good_for_env ls then
      let tydisl = option_apply tyl (fun e -> e::tyl) tyv in
      let lsinst = create_lsymbol (id_clone ls.ls_name) tyl tyv in
      let insts = Mls.find_default ls Mtyl.empty env in
      Mls.add ls (Mtyl.add tydisl lsinst insts) env
    else env

  let fold_add_instantion task env = match task.task_decl.td_node with
    | Decl { d_node = Dprop (_,_,f)} -> t_app_fold add_mono_instantiation env f
    | _ -> env

(** completion functions *)
  let env_from_only_kept_lskept env kept lskept =
    let fold_ls ls env =
      let rec aux insts tydisl subst = function
        | [] ->
          let tydisl = List.rev tydisl in
          let tyl,tyv = match tydisl, ls.ls_value with
            | tyv::tyl, Some _ -> tyl,Some tyv
            | tyl, None -> tyl,None
            | _ -> assert false in
          let lsinst = create_lsymbol (id_clone ls.ls_name) tyl tyv in
          Mtyl.add tydisl lsinst insts
        | ty::tyl ->
          let fold_ty tykept insts =
            try
              let subst = ty_match subst ty tykept in
              aux insts (tykept::tydisl) subst tyl
            with TypeMismatch _ -> insts
          in
          Sty.fold fold_ty kept insts
      in
      let lsty = option_apply ls.ls_args (fun e -> e::ls.ls_args) ls.ls_value
      in
      let insts = aux Mtyl.empty  [] Mtv.empty lsty in
      Mls.add ls insts env
    in
    Sls.fold fold_ls lskept env

  let env_from_not_only_kept_lskept env kept lskept =
    (** complete by subterm *)
    let fold ty acc =
      let rec add acc ty = ty_fold add (Sty.add ty acc) ty in
      add acc ty in
    let kept = Sty.fold fold kept kept in
    env_from_only_kept_lskept env kept lskept

end

include Lskept
include Kept
include Env

let register pr l = List.iter (fun (n,f) -> Hashtbl.replace pr n f) l
let register pr nothing goal all =
  register pr ["nothing",nothing; "goal",goal; "all",all]


(** {2 select instantiation} *)
(** add nothing *)
 (* TODO : create for each right inst a new logic *)
let inst_nothing _env = Trans.identity

(** goal *)
let inst_goal _env =
  Trans.compose (inst_nothing _env) $
  Trans.tgoal (fun pr f ->
    let env = t_app_fold add_mono_instantiation Mls.empty f in
    let decls = [create_decl (create_prop_decl Pgoal pr f)] in
    let decls = meta_kept_from_env decls env in
    metas_of_env env decls)


(** goal + context *)
let inst_all _env =
  Trans.compose (inst_nothing _env) $
  Trans.bind (Trans.fold fold_add_instantion Mls.empty)
    (fun env ->
      let decls = meta_kept_from_env [] env in
      Trans.add_tdecls (metas_of_env env decls))

(** register *)
let () = register ft_select_lsinst inst_nothing inst_goal inst_all

(** {2 select Kept} *)
(** add nothing *)
let kept_nothing _env = Trans.identity

(** goal *)
let kept_goal _env =
  Trans.tgoal (fun pr f ->
    let kept = t_app_fold add_mono_kept Sty.empty f in
    metas_of_kept kept [create_decl (create_prop_decl Pgoal pr f)])

(** goal + context *)
let kept_all _env =
  Trans.bind (Trans.fold fold_add_kept Sty.empty)
    (fun kept -> Trans.add_tdecls (metas_of_kept kept []))

(** register *)
let () = register ft_select_kept kept_nothing kept_goal kept_all

(** {2 select Lskept} *)
(** add nothing *)
let lskept_nothing _env = Trans.identity

(** goal *)
let lskept_goal _env =
  Trans.tgoal (fun pr f ->
    let lskept = t_app_fold add_mono_lskept Sls.empty f in
    metas_of_lskept lskept [create_decl (create_prop_decl Pgoal pr f)])

(** goal + context *)
let lskept_all _env =
  Trans.bind (Trans.fold fold_add_lskept Sls.empty)
    (fun lskept -> Trans.add_tdecls (metas_of_lskept lskept []))

(** register *)
let () = register ft_select_lskept lskept_nothing lskept_goal lskept_all

(** completion is a bad name in dont remember the good one *)
(** {2 Completion "Lskept x Kept" to add to Instantiation} *)
let completion_lskept_only_kept _env =
  Trans.on_tagged_ls meta_lskept (fun lskept ->
    Trans.on_tagged_ty meta_kept (fun kept ->
      let env = env_from_only_kept_lskept empty_env kept lskept in
      Trans.add_tdecls (metas_of_env env [])))

let completion_lskept_some_kept _env =
  Trans.on_tagged_ls meta_lskept (fun lskept ->
    Trans.on_tagged_ty meta_kept (fun kept ->
      let env = env_from_not_only_kept_lskept empty_env kept lskept in
      Trans.add_tdecls (metas_of_env env [])))

let () =
  Hashtbl.replace ft_completion_mode "nothing"   (fun _ -> Trans.identity)
let () =
  Hashtbl.replace ft_completion_mode "only_kept" completion_lskept_only_kept
let () =
  Hashtbl.replace ft_completion_mode "some_kept" completion_lskept_some_kept

(*
Local Variables:
compile-command: "unset LANG; make -j -C ../.. byte"
End:
*)
