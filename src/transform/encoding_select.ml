(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ty
open Ident
open Term
open Decl
open Theory
open Task
open Encoding
open Discriminate

let register pr l = List.iter (fun (n,f) -> Hstr.replace pr n (Util.const f)) l

let register pr none goal local all =
  register pr ["none",none; "goal",goal; "local",local; "all",all]

(** {2 select Kept} *)

let trans_on_goal fn = Trans.store (function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (_,_,f) }}} -> fn f
  | _ -> assert false)

let is_local = function
  | {d_node = Dprop (Pgoal,_,_)} ->
      true
  | {d_node =
      ( Dparam ({ls_args = []; ls_value = Some _} as ls)
      | Dlogic [{ls_args = []; ls_value = Some _} as ls, _])} ->
      Ident.Sattr.mem Inlining.intro_attr ls.ls_name.id_attrs
  | {d_node = Dprop (Paxiom, pr, _)} ->
      Ident.Sattr.mem Inlining.intro_attr pr.pr_name.id_attrs
  | _ ->
      false

module Kept = struct
  (* we ignore the type of the result as we are
     only interested in application arguments *)
  let add_kept_app sty _ls tyl _tyv =
    let add sty ty = if ty_closed ty then Sty.add ty sty else sty in
    List.fold_left add sty tyl

  let add_kept_case sty ts tyl _ =
    let ty = ty_app ts tyl in
    if ty_closed ty then Sty.add ty sty else sty

  let add_kept sty t =
    let sty = t_app_fold add_kept_app sty t in
    t_case_fold add_kept_case sty t

  let local_kept task sty = match task.task_decl.td_node with
    | Decl d when is_local d -> decl_fold add_kept sty d
    | _ -> sty

  let all_kept task sty = match task.task_decl.td_node with
    | Decl d -> decl_fold add_kept sty d
    | _ -> sty

  let kept_none = Trans.return Sty.empty
  let kept_goal = trans_on_goal (add_kept Sty.empty)
  let kept_local = Trans.fold local_kept Sty.empty
  let kept_all  = Trans.fold all_kept Sty.empty

  let () = register ft_select_kept kept_none kept_goal kept_local kept_all
  let () = register ft_select_inst kept_none kept_goal kept_local kept_all
end

(** {2 select Lskept} *)

module Lskept = struct

  let add_lskept sls ls =
    (* We require that every freely standing type variable occurs
       under a type constructor elsewhere in the lsymbol's signature.
       Thus we bound the (lskept * inst) product and avoid explosion. *)
    let ls_sig = oty_cons ls.ls_args ls.ls_value in
    let add_ty_t s ty = match ty.ty_node with
      | Tyapp _ -> ty_freevars s ty | _ -> s in
    let ls_tvs_t = List.fold_left add_ty_t Stv.empty ls_sig in
    if Stv.is_empty ls_tvs_t then sls else
    let add_ty_v s ty = match ty.ty_node with
      | Tyvar v -> Stv.add v s | _ -> s in
    let ls_tvs_v = List.fold_left add_ty_v Stv.empty ls_sig in
    if Stv.subset ls_tvs_v ls_tvs_t then Sls.add ls sls else sls

  let local_lskept task sls = match task.task_decl.td_node with
    | Decl ({ d_node = Dparam ls } as d) when is_local d ->
        add_lskept sls ls
    | Decl ({ d_node = Dlogic l } as d) when is_local d ->
        List.fold_left (fun sls (ls,_) -> add_lskept sls ls) sls l
    | _ -> sls

  let all_lskept task sls = match task.task_decl.td_node with
    | Decl { d_node = Dparam ls } ->
        add_lskept sls ls
    | Decl { d_node = Dlogic l } ->
        List.fold_left (fun sls (ls,_) -> add_lskept sls ls) sls l
    | _ -> sls

  let add_lskept = t_app_fold (fun sls ls _ _ -> add_lskept sls ls)

  let lskept_none = Trans.return Sls.empty
  let lskept_goal = trans_on_goal (add_lskept Sls.empty)
  let lskept_local = Trans.fold local_lskept Sls.empty
  let lskept_all  = Trans.fold all_lskept Sls.empty

  let () =
    register ft_select_lskept lskept_none lskept_goal lskept_local lskept_all
end

(** {2 select Lsinst} *)

module Lsinst = struct

  let add_lsinst mls ls tyl tyv =
    if ls_equal ls ps_equ ||
      List.for_all ty_closed (oty_cons ls.ls_args ls.ls_value) ||
      List.exists (fun ty -> not (ty_closed ty)) (oty_cons tyl tyv)
    then mls else Lsmap.add ls tyl tyv mls

  let add_lsinst mls t = t_app_fold add_lsinst mls t

  let local_lsinst task mls = match task.task_decl.td_node with
    | Decl d when is_local d -> decl_fold add_lsinst mls d
    | _ -> mls

  let all_lsinst task mls = match task.task_decl.td_node with
    | Decl d -> decl_fold add_lsinst mls d
    | _ -> mls

  let lsinst_none = Trans.return Lsmap.empty
  let lsinst_goal = trans_on_goal (add_lsinst Lsmap.empty)
  let lsinst_local = Trans.fold local_lsinst Lsmap.empty
  let lsinst_all  = Trans.fold all_lsinst Lsmap.empty

  let () =
    register ft_select_lsinst lsinst_none lsinst_goal lsinst_local lsinst_all
end

(** {2 select Alginst} *)

module Alginst = struct
  let add ts tyl m =
    let styl = Mts.find_def Styl.empty ts m in
    Mts.add ts (Styl.add tyl styl) m

  let add_alginst_app acc ls tyl tyv =
    if ls_equal ls ps_equ ||
       List.exists (fun ty -> not (ty_closed ty)) (oty_cons tyl tyv)then acc
    else if ls.ls_constr > 0 then
      match tyv with
      | Some ({ty_node = Tyapp (tys, tyl)}) -> add tys tyl acc
      | _ -> assert false
    else if ls.ls_proj then
      match tyl with
      | [{ty_node = Tyapp (tys, tyl)}] -> add tys tyl acc
      | _ -> assert false
    else acc

  let add_alginst_case acc tys tyl _ =
    if tyl = [] || List.exists (fun ty -> not (ty_closed ty)) tyl then acc
    else add tys tyl acc

  let add_alginst_term acc t =
    let acc = t_app_fold add_alginst_app acc t in
    t_case_fold add_alginst_case acc t

  let local_alginst task acc = match task.task_decl.td_node with
    | Decl d when is_local d -> decl_fold add_alginst_term acc d
    | _ -> acc

  let all_alginst task acc = match task.task_decl.td_node with
    | Decl d -> decl_fold add_alginst_term acc d
    | _ -> acc

  let alginst_none = Trans.return Mts.empty
  let alginst_goal = trans_on_goal (add_alginst_term Mts.empty)
  let alginst_local = Trans.fold local_alginst Mts.empty
  let alginst_all  = Trans.fold all_alginst Mts.empty

  let () =
    register ft_select_alginst alginst_none alginst_goal alginst_local alginst_all
end
