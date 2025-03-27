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
open Ident
open Ty
open Term
open Decl
open Theory
open Task

module OHTyl = OrderedHashedList(struct
  type t = ty
  let tag = ty_hash
end)
module Mtyl = Extmap.Make(OHTyl)

type tenv = {
  specials : tysymbol Mty.t;
  trans_lsymbol : lsymbol Mtyl.t Mls.t;
  undefined : (tysymbol * ty) list;
}

let init_tenv = {
  specials = Mty.empty;
  trans_lsymbol = Mls.empty;
  undefined = [];
}

(* Convert type *)
let conv_ts tenv name ty =
  let tenv, ts =
    try tenv,Mty.find ty tenv.specials
    with Not_found ->
      let ts = create_tysymbol (id_clone name) [] NoDef in
      { tenv with specials=Mty.add ty ts tenv.specials },ts
  in
  { tenv with undefined=(ts,ty)::tenv.undefined },ts

let conv_ty tenv ty =
  if not (ty_closed ty) then
    Printer.unsupportedType ty "type variable must be encoded";
  match ty.ty_node with
  | Tyapp (_,[]) -> tenv,ty
  | Tyapp (ts,_) ->
    let tenv,ts = conv_ts tenv ts.ts_name ty in
    tenv,ty_app ts []
  | _ -> assert false

(* Convert a variable *)
let conv_vs tenv vs =
  let tenv,ty = conv_ty tenv vs.vs_ty in
  if ty_equal ty vs.vs_ty then tenv,vs else
  tenv,create_vsymbol (id_clone vs.vs_name) ty

(* Convert a logic symbol to the encoded one *)
let conv_ls tenv ls tyl tyv =
  if ls_equal ls ps_equ then tenv,ls
  else
    (* We must call conv_ty even if the lsymbol is known, to update the
       undefined list (in the meta case, the undefined list is dropped, so we
       may have added the lsymbol to trans_lsymbol without having declared the
       types). )
     *)
    let tenv,ty_res = Opt.map_fold conv_ty tenv tyv in
    let tenv,ty_arg = Lists.map_fold_left conv_ty tenv tyl in
    match Mtyl.find (oty_cons tyl tyv) (Mls.find ls tenv.trans_lsymbol) with
    | ls -> tenv,ls
    | exception Not_found ->
      ignore (List.fold_left2 ty_match Mtv.empty (oty_cons ls.ls_args ls.ls_value) (oty_cons tyl tyv));
      let ls' =
        if Option.equal ty_equal ty_res ls.ls_value &&
           List.for_all2 ty_equal ty_arg ls.ls_args then ls
        else create_lsymbol ~constr:ls.ls_constr ~proj:ls.ls_proj
                            (id_clone ls.ls_name) ty_arg ty_res
      in
      let m = Mls.find_def Mtyl.empty ls tenv.trans_lsymbol in
      let m = Mls.add ls (Mtyl.add (oty_cons tyl tyv) ls' m) tenv.trans_lsymbol in
      { tenv with trans_lsymbol = m },ls'

let rec rewrite vm tenv t =
  match t.t_node with
  | Tconst _ -> tenv,t
  | Tvar x -> tenv,Mvs.find x vm
  | Tapp (ps,tl) when ls_equal ps ps_equ ->
      let tenv,tl = Lists.map_fold_left (rewrite vm) tenv tl in
      tenv,ps_app ps tl
  | Tapp (ls,tl) ->
      let tenv,ls = conv_ls tenv ls (List.map (fun t -> Option.get t.t_ty) tl) t.t_ty in
      let tenv,tl = Lists.map_fold_left (rewrite vm) tenv tl in
      tenv,t_app ls tl ls.ls_value
  | Tif (f, t1, t2) ->
      let tenv,f = rewrite vm tenv f in
      let tenv,t1 = rewrite vm tenv t1 in
      let tenv,t2 = rewrite vm tenv t2 in
      tenv,t_if f t1 t2
  | Tlet (t1, b) ->
      let u,t2,close = t_open_bound_cb b in
      let tenv,u' = conv_vs tenv u in
      let tenv,t1' = rewrite vm tenv t1 in
      let tenv,t2' = rewrite (Mvs.add u (t_var u') vm) tenv t2 in
      tenv,t_let t1' (close u' t2')
  | Tcase (t, bl) ->
      let rw_b tenv b =
        let p,tb,close = t_open_branch_cb b in
        let tenv,vm,p =
          match p.pat_node with
          | Pwild -> let tenv,ty = conv_ty tenv p.pat_ty in tenv,vm,pat_wild ty
          | Papp (ls, pl) ->
            let tenv,ls = conv_ls tenv ls (List.map (fun p -> p.pat_ty) pl) t.t_ty in
            let add (tenv,m) = function
              | { pat_node = Pvar v } ->
                let tenv,v' = conv_vs tenv v in
                (tenv,Mvs.add v (t_var v') m),pat_var v'
              | _ -> Printer.unsupportedTerm t "unsupported term"
            in
            let (tenv,vm),pl = Lists.map_fold_left add (tenv,vm) pl in
            tenv,vm,pat_app ls pl (Option.get ls.ls_value)
          | _ -> Printer.unsupportedTerm t "unsupported term"
        in
        let tenv,tb = rewrite vm tenv tb in
        tenv,close p tb
      in
      let tenv,t = rewrite vm tenv t in
      let tenv,bl = Lists.map_fold_left rw_b tenv bl in
      tenv,t_case t bl
  | Tquant (q,b) ->
      let vl, tl, f1, close = t_open_quant_cb b in
      let add (tenv,m) v =
        let tenv,v' = conv_vs tenv v in (tenv,Mvs.add v (t_var v') m), v'
      in
      let (tenv,vm), vl' = Lists.map_fold_left add (tenv,vm) vl in
      let tenv,tl' = tr_map_fold (rewrite vm) tenv tl in
      let tenv,f1' = rewrite vm tenv f1 in
      tenv,t_quant q (close vl' tl' f1')
  | Teps _ ->
      Printer.unsupportedTerm t "unsupported term"
  | _ -> t_map_fold (rewrite vm) tenv t

let decl_ud alg_kept tenv kn task =
  let rec go tenv task dm =
    match tenv.undefined with
    | [] -> (tenv,task,dm)
    | (ts, ty0) :: undefined ->
      let tenv = { tenv with undefined } in
      if Mid.mem ts.ts_name (task_known task) || Mts.mem ts dm then go tenv task dm
      else let mono = match ty0.ty_node with Tyapp(_,[]) -> true | _ -> false in
      if not (mono || Sty.mem ty0 alg_kept) then go tenv (add_ty_decl task ts) dm
      else match ty0.ty_node with
      | Tyapp(ts0, _) ->
        begin match Mid.find ts0.ts_name kn with
        | { d_node = Ddata dl0 } ->
          let (_, csl) = List.find (fun d -> ts_equal (fst d) ts0) dl0 in
          let sigma =
            Ty.ty_match Mtv.empty (ty_app ts0 (List.map ty_var ts0.ts_args)) ty0
          in
          let map_c tenv (c, pjs) =
            let tenv,c =
              conv_ls tenv c (List.map (Ty.ty_inst sigma) c.ls_args) (Some ty0)
            in
            let conv_p tenv = function
            | None -> tenv,None
            | Some p ->
              let tenv,p = conv_ls tenv p [ty0] (Ty.oty_inst sigma p.ls_value) in
              tenv,Some p
            in
            let tenv,pjs = Lists.map_fold_left conv_p tenv pjs in
            tenv, (c, pjs) in
          let tenv,csl = Lists.map_fold_left map_c tenv csl in
          go tenv task (Mts.add ts csl dm)
        | _ -> assert false
        end
       | _ -> assert false
  in
  let tenv,task,dm = go tenv task Mts.empty in
  let dl = Mts.bindings dm in
  if dl = [] then tenv,task else tenv,add_data_decl task dl

let fold alg_kept taskpre (tenv,task) =
  assert (tenv.undefined = []);
  match taskpre.task_decl.td_node with
    | Decl d ->
      begin match d.d_node with
        | Dtype { ts_def = Alias _ }
        | Dtype { ts_args = _::_ } -> tenv,task
        | Dtype ts -> tenv,add_ty_decl task ts
        | Ddata dl ->
          let get_ty (ts, _) =
            if ts.ts_args = [] then Some (ts, ty_app ts []) else None
          in
          let tenv = { tenv with undefined = List.filter_map get_ty dl } in
          decl_ud alg_kept tenv taskpre.task_known task
        | Dparam ls ->
          let tenv,ls = conv_ls tenv ls ls.ls_args ls.ls_value in
          let tenv,task = decl_ud alg_kept tenv taskpre.task_known task in
          tenv,add_param_decl task ls
        | Dlogic ll ->
          let conv_def tenv (ls,def) =
            let tenv,ls = conv_ls tenv ls ls.ls_args ls.ls_value in
            let vl,t,close = open_ls_defn_cb def in
            let add (tenv,m) v =
              let tenv,v' = conv_vs tenv v in (tenv,Mvs.add v (t_var v') m), v'
            in
            let (tenv,m),vl = Lists.map_fold_left add (tenv,Mvs.empty) vl in
            let tenv,t = rewrite m tenv t in
            tenv,close ls vl t
          in
          let tenv,ll = Lists.map_fold_left conv_def tenv ll in
          let tenv,task = decl_ud alg_kept tenv taskpre.task_known task in
          tenv,add_logic_decl task ll
        | Dind _ ->
          Printer.unsupportedDecl d "use eliminate_inductive"
        | Dprop _ ->
          let tenv, d = Decl.decl_map_fold (rewrite Mvs.empty) tenv d in
          let tenv,task = decl_ud alg_kept tenv taskpre.task_known task in
          tenv,add_decl task d
      end
    | Meta(meta,ml) ->
      begin try
        let map tenv = function
          | MAty ty -> let tenv,ty = conv_ty tenv ty in tenv,MAty ty
          | MAts {ts_name = name; ts_args = []; ts_def = Alias ty} ->
              let tenv,ts = conv_ts tenv name ty in tenv,MAts ts
          | MAts {ts_args = []} as x -> tenv,x
          | MAts _ -> raise Exit
          | MAls ls ->
             (* FIXME: this forbids metas on projections or constructors of
                polymorphic algebraic types. *)
             let tenv,ls = conv_ls tenv ls ls.ls_args ls.ls_value in
             tenv, MAls ls
          | MApr _ -> raise Exit
          | MAstr _ as s -> tenv,s
          | MAint _ as i -> tenv,i
          | MAid _ as i -> tenv,i
        in
        let tenv,arg = Lists.map_fold_left map tenv ml in
        (* We completely ignore the undefined list, because metas
           may refer to types that are not defined yet. *)
        let tenv = { tenv with undefined = [] } in
        tenv,add_meta task meta arg
      with
        | Printer.UnsupportedType _
        | Exit -> tenv,add_tdecl task taskpre.task_decl
      end
    | _ -> tenv,add_tdecl task taskpre.task_decl

let t =
  Trans.on_tagged_ty Eliminate_algebraic.meta_alg_kept (fun alg_kept ->
      Trans.fold_map (fold alg_kept) init_tenv None)

let () = Trans.register_transform "encoding_sort" t
  ~desc:"Replace@ every@ closed@ type@ by@ a@ separate@ type@ constant."
