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

(* First implementation by Jacques-Pascal Deplaix
   during an internship at LRI, May-August 2014 *)

open Ty
open Ident
open Term
open Decl

type t = {
  driver      : Mlw_driver.driver;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  is_exec_id  : bool Hid.t;             (* cache *)
}

let create dr thkm mokm =
  { driver = dr;
    th_known_map = thkm;
    mo_known_map = mokm;
    is_exec_id = Hid.create 17; }

let has_syntax ctx id =
  Mid.mem id ctx.driver.Mlw_driver.drv_syntax ||
  Mid.mem id ctx.driver.Mlw_driver.drv_converter

let is_exec_id ctx id f =
  try
    Hid.find ctx.is_exec_id id
  with Not_found ->
    let b = has_syntax ctx id || f ctx id in Hid.add ctx.is_exec_id id b; b

let declare_id ctx id b =
  Hid.add ctx.is_exec_id id b

(** Logic *)

let is_exec_const = function
  | Number.ConstInt _ -> true
  | Number.ConstReal _ -> false

let rec is_exec_term ctx t = match t.t_node with
  | Ttrue
  | Tfalse
  | Tvar _ ->
      true
  | Tconst c ->
      is_exec_const c
  | Tapp (ls, tl) when ls.ls_constr > 0 ->
      begin match try Some (Mlw_expr.restore_pl ls) with Not_found -> None with
      | Some pl ->
          let test fd arg = fd.Mlw_expr.fd_ghost || is_exec_term ctx arg in
          List.for_all2 test pl.Mlw_expr.pl_args tl
      | None -> List.for_all (is_exec_term ctx) tl
      end
  | Tapp (ls, tl) ->
      is_exec_lsymbol ctx ls && List.for_all (is_exec_term ctx) tl
  | Tif (t1, t2, t3) ->
      is_exec_term ctx t1 && is_exec_term ctx t2 && is_exec_term ctx t3
  | Tbinop (_, t1, t2) ->
      is_exec_term ctx t1 && is_exec_term ctx t2
  | Tnot t ->
      is_exec_term ctx t
  | Tlet (t1, b2) ->
      is_exec_term ctx t1 && is_exec_bound ctx b2
  | Tcase (t1, bl) ->
      is_exec_term ctx t1 && List.for_all (is_exec_branch ctx) bl
  | Teps _ when t_is_lambda t ->
      let _, _, t1 = t_open_lambda t in is_exec_term ctx t1
  | Teps _ | Tquant _ ->
      false

and is_exec_branch ctx b =
  let _, t = t_open_branch b in is_exec_term ctx t

and is_exec_bound ctx b =
  let _, t = t_open_bound b in is_exec_term ctx t

and is_exec_lsymbol ctx ls =
  is_exec_id ctx ls.ls_name
    (fun _ _ -> match Mid.find_opt ls.ls_name ctx.th_known_map with
      | None   -> false
      | Some d -> ignore (is_exec_decl ctx d); is_exec_lsymbol ctx ls)

and is_exec_decl ctx d =
  let allow_ts ts = declare_id ctx ts.ts_name true in
  let allow_ls ls = declare_id ctx ls.ls_name true in
  let forbid_ls ls = declare_id ctx ls.ls_name false in
  match d.d_node with
  | Dtype ts ->
      allow_ts ts; true
  | Ddata ddl ->
      let constructor (ls, prl) =
        allow_ls ls; List.iter (Opt.iter allow_ls) prl in
      let declare (ts, cl) =
        allow_ts ts; List.iter constructor cl in
      List.iter declare ddl; true
  | Dparam ls ->
      forbid_ls ls; false
  | Dlogic ll ->
      List.iter (fun (ls, _) -> allow_ls ls) ll;
      List.for_all
        (fun (_, ld) -> is_exec_term ctx (snd (open_ls_defn ld))) ll ||
      begin List.iter (fun (ls, _) -> forbid_ls ls) ll; false end
      (* TODO? we could be more precise if two definitions are
         unnecessarily recursive and one is executable and the other is not *)
  | Dind (_, l) ->
      List.iter (fun (ls, _) -> forbid_ls ls) l; false
  | Dprop _ ->
      false

open Mlw_ty
open Mlw_expr
open Mlw_decl

let rec is_exec_expr ctx e =
  not e.e_ghost &&
  match e.e_node with
    | Eassert _
    | Eabsurd
    | Evalue _
    | Earrow _ ->
        true
    | Eany _ ->
        false
    | Elogic t ->
        is_exec_term ctx t
    | Eloop (_, _, e1)
    | Efor (_, _, _, e1)
    | Eraise (_, e1)
    | Eapp (e1, _, _)
    | Eabstr (e1, _)
    | Eassign (_, e1, _, _) ->
        is_exec_expr ctx e1
    | Elet ({let_expr = e1; _}, e2) when e1.e_ghost ->
        is_exec_expr ctx e2
    | Elet ({let_expr = e1; _}, e2) ->
        is_exec_expr ctx e1 &&
        is_exec_expr ctx e2
    | Eif (e0, e1, e2) ->
        is_exec_expr ctx e0 &&
        is_exec_expr ctx e1 &&
        is_exec_expr ctx e2
    | Erec (fdl, e1) ->
        let aux f = is_exec_expr ctx f.fun_lambda.l_expr in
        List.for_all aux fdl &&
        is_exec_expr ctx e1
    | Ecase (e1, [_, e2]) when e1.e_ghost ->
        is_exec_expr ctx e2
    | Ecase (e1, bl) ->
        let aux (_, e) = is_exec_expr ctx e in
        is_exec_expr ctx e1 &&
        List.for_all aux bl
    | Etry (e1, bl) ->
        let aux (_, _, e) = is_exec_expr ctx e in
        is_exec_expr ctx e1 &&
        List.for_all aux bl
    | Eghost _ ->
        assert false

let is_ghost_lv = function
  | LetV pv -> pv.pv_ghost
  | LetA ps -> ps.ps_ghost

let is_exec_pdecl ctx pd = match pd.pd_node with
  | PDtype _
  | PDexn _
  | PDdata _ ->
      true
  | PDlet {let_sym = lv; _}
  | PDval lv when is_ghost_lv lv ->
      false
  | PDval (LetV {pv_vs = {vs_name = name}; _} | LetA {ps_name = name; _}) ->
      has_syntax ctx name
  | PDlet ld ->
      is_exec_expr ctx ld.let_expr
  | PDrec fdl ->
      let aux f = is_exec_expr ctx f.fun_lambda.l_expr in
      List.for_all aux fdl
