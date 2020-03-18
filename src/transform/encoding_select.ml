(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ty
open Term
open Decl
open Theory
open Task
open Encoding
open Discriminate

let register pr l = List.iter (fun (n,f) -> Hstr.replace pr n (Util.const f)) l

let register pr none goal all =
  register pr ["none",none; "goal",goal; "all",all]

(** {2 select Kept} *)

let trans_on_goal fn = Trans.store (function
  | Some { task_decl = { td_node = Decl { d_node = Dprop (_,_,f) }}} -> fn f
  | _ -> assert false)

module Kept = struct
  (* we ignore the type of the result as we are
     only interested in application arguments *)
  let add_kept sty _ls tyl _tyv =
    let add sty ty = if ty_closed ty then Sty.add ty sty else sty in
    List.fold_left add sty tyl

  let add_kept = t_app_fold add_kept

  let all_kept task sty = match task.task_decl.td_node with
    | Decl d -> decl_fold add_kept sty d
    | _ -> sty

  let kept_none = Trans.return Sty.empty
  let kept_goal = trans_on_goal (add_kept Sty.empty)
  let kept_all  = Trans.fold all_kept Sty.empty

  let () = register ft_select_kept kept_none kept_goal kept_all
  let () = register ft_select_inst kept_none kept_goal kept_all
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

  let all_lskept task sls = match task.task_decl.td_node with
    | Decl { d_node = Dparam ls } ->
        add_lskept sls ls
    | Decl { d_node = Dlogic l } ->
        List.fold_left (fun sls (ls,_) -> add_lskept sls ls) sls l
    | _ -> sls

  let add_lskept = t_app_fold (fun sls ls _ _ -> add_lskept sls ls)

  let lskept_none = Trans.return Sls.empty
  let lskept_goal = trans_on_goal (add_lskept Sls.empty)
  let lskept_all  = Trans.fold all_lskept Sls.empty

  let () = register ft_select_lskept lskept_none lskept_goal lskept_all
end

(** {2 select Lsinst} *)

module Lsinst = struct

  let add_lsinst mls ls tyl tyv =
    if ls_equal ls ps_equ ||
      List.for_all ty_closed (oty_cons ls.ls_args ls.ls_value) ||
      List.exists (fun ty -> not (ty_closed ty)) (oty_cons tyl tyv)
    then mls else Lsmap.add ls tyl tyv mls

  let add_lsinst mls t = t_app_fold add_lsinst mls t

  let all_lsinst task mls = match task.task_decl.td_node with
    | Decl d -> decl_fold add_lsinst mls d
    | _ -> mls

  let lsinst_none = Trans.return Lsmap.empty
  let lsinst_goal = trans_on_goal (add_lsinst Lsmap.empty)
  let lsinst_all  = Trans.fold all_lsinst Lsmap.empty

  let () = register ft_select_lsinst lsinst_none lsinst_goal lsinst_all
end
