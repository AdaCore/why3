(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Decl
open Theory
open Ty

let debug = Debug.register_info_flag "eliminate_unknown_types"
  ~desc:"Print@ debugging@ messages@ of@ the@ eliminate_unknown_types@ transformation."

let syntactic_transform =
  Trans.on_meta Printer.meta_syntax_type (fun metas ->
      let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [MAts ts; MAstr _; MAint _] -> Sts.add ts acc
      | _ -> assert false) Sts.empty metas in
      Trans.return (fun ts -> Sts.mem ts symbols))

let remove_terms keep =
  let keep_ls ls =
    (* check that we want to keep all the types occurring in the type
       of ls *)
    List.for_all (fun ty -> ty_s_all keep ty) ls.ls_args
    &&
    begin match ls.ls_value with
      | Some ty -> ty_s_all keep ty
      | None -> true            (* bool are kept by default *)
    end
  in
  let keep_term (t:term) =
    t_s_all (fun ty -> ty_s_all keep ty) (fun _ -> true) t
    &&
    begin match t.t_ty with
      | Some t -> ty_s_all keep t
      | None -> true
    end
  in
  (* let already_removed = ref Sls.empty in*)
  let is_removed already_removed =
    Term.t_fold (fun acc t ->
        match t.t_node with
        | Tapp (ls, _) -> Sls.mem ls already_removed || acc
        | _ -> acc) false
  in

  Trans.fold (fun hd (already_removed, task_uc) ->
      match hd.Task.task_decl.td_node with
      | Decl d ->
          begin match d.d_node with
          | Dtype ty when not (keep ty) ->
              Debug.dprintf debug "remove@ type@ %a@." Pretty.print_ty_decl ty;
              (already_removed, task_uc)
          | Ddata l  when List.exists (fun (t,_) -> not (keep t)) l ->
              Debug.dprintf debug "remove@ data@ %a@." Pretty.print_data_decl (List.hd l);
              (already_removed, task_uc)
          | Dparam l when not (keep_ls l) ->
              let already_removed = Sls.add l already_removed in
              Debug.dprintf debug "remove@ param@ %a@." Pretty.print_ls l;
              (already_removed, task_uc)
          | Dlogic l when
              List.exists (fun (l,def) -> not (keep_ls l) ||
                                          let (_, t) = open_ls_defn def in
                                          not (keep_term t) || is_removed already_removed t) l ->
              let already_removed =
                List.fold_left (fun acc (ls, _) -> Sls.add ls acc) already_removed l
              in
              Debug.dprintf debug "remove@ logic@ %a@." Pretty.print_logic_decl (List.hd l);
              (already_removed, task_uc)
          | Dprop (Pgoal,pr,t) when not (keep_term t) || is_removed already_removed t ->
              Debug.dprintf debug "change@ goal@ %a@." Pretty.print_term t;
              let task_uc =
                Task.add_decl task_uc (create_prop_decl Pgoal pr t_false) in
              (already_removed, task_uc)
          | Dprop (_,_,t) when not (keep_term t) || is_removed already_removed t ->
              Debug.dprintf debug "remove@ prop@ %a@." Pretty.print_term t;
              (already_removed, task_uc)
          | _ -> (already_removed, Task.add_decl task_uc d)
          end
      | _ -> (already_removed, Task.add_tdecl task_uc hd.Task.task_decl)
    )
    (Sls.empty, None)

let remove_types =
  (* TODO fix the pair *)
  Trans.bind (Trans.bind syntactic_transform remove_terms)
    (fun (_, task) -> Trans.return task)

let () =
  Trans.register_transform "eliminate_unknown_types" remove_types
    ~desc:"Remove@ types@ unknown@ to@ the@ prover@ and@ terms@ referring@ to@ them."


let remove_ty_constr keep =
  let keep ts =
    match ts.Ty.ts_args with | [] -> true | _ -> keep ts
  in
  let keep_ty ty =
    Ty.ty_all (fun ty ->
        match ty.ty_node with
        | Ty.Tyvar _ -> invalid_arg "remove_ty_constr used with polymorphism"
        | Ty.Tyapp (ts, _) -> keep ts)
      ty
  in
  let keep_ls ls =
    List.for_all keep_ty ls.Term.ls_args
    && Opt.for_all keep_ty ls.Term.ls_value
  in
  let keep_term t =
    Term.t_s_all keep_ty keep_ls t
  in
  let convert db ty ts =
    let (m,new_)  = !db in
    match Mty.find_opt ty m with
    | None ->
        let s = Pp.sprintf_wnl "%a" Pretty.print_ty ty in
        let ts = Ty.create_tysymbol (Ident.id_derive s ts.Ty.ts_name) [] NoDef in
        let ty' = Ty.ty_app ts [] in
        db := (Mty.add ty ty' m,ts::new_);
        ty'
    | Some ty -> ty
  in
  let rec map' db (ty:Ty.ty) =
    match ty.ty_node with
    | Ty.Tyvar _ -> invalid_arg "remove_ty_constr used with polymorphism"
    | Ty.Tyapp (ts, _) when (keep ts) ->
        Ty.ty_map (map' db) ty
    | Ty.Tyapp (ts, _)  ->
        convert db ty ts
  in
  let map (mty,new_)  ty =
    let db = ref (mty,new_) in
    let ty = map' db ty in
    !db, ty
  in
  let map_term mty mls mvs new_ t =
    let db = ref (mty,new_) in
    let t =
      Term.t_gen_map
        (map' db)
        (fun ls -> Mls.find_def ls ls mls)
        mvs
        t
    in
    let (mty,new_) = !db in
    (mty,mls,new_,t)
  in
  let create_new_ls mty mls new_ ls =
    let id = Ident.id_clone ls.ls_name in
    let db = (mty,new_) in
    let db,args = Lists.map_fold_left map db ls.Term.ls_args in
    let (mty,new_),value = Opt.map_fold map db ls.Term.ls_value in
    let ls' = Term.create_lsymbol id args value in
    let mls = Mls.add ls ls' mls in
    (mty,mls,new_,ls')
  in
  let add_new mty mls new_ task_uc d =
    let task_uc =
      List.fold_left (fun task_uc ts -> Task.add_decl task_uc (create_ty_decl ts))
        task_uc new_ in
    ((mty,mls), Task.add_decl task_uc d)
  in
  Trans.fold (fun hd ((mty,mls),task_uc) ->
      match hd.Task.task_decl.td_node with
      | Decl d ->
          begin match d.d_node with
          | Dtype ty when not (keep ty) ->
              Debug.dprintf debug "remove@ type@ %a@." Pretty.print_ty_decl ty;
              ((mty,mls), task_uc)
          | Ddata l  when List.exists (fun (t,_) -> not (keep t)) l ->
              invalid_arg "remove_ty_constr with datatype with constructor"
          | Dparam ls when not (keep_ls ls) ->
              let (mty,mls,new_,ls) = create_new_ls mty mls [] ls in
              let d = create_param_decl ls in
              add_new mty mls new_ task_uc d
          | Dlogic l when not
                (List.for_all (fun (l,def) ->
                     (keep_ls l) &&
                     let (_, t) = open_ls_defn def in
                     keep_term t) l) ->
              let ((mty,mls,new_),l) =
                Lists.map_fold_left
                  (fun (mty,mls,new_) (ls,def) ->
                     let (mty,mls,new_,ls) = create_new_ls mty mls new_ ls in
                     ((mty,mls,new_),(ls,def))
                  )
                  (mty,mls,[]) l
              in
              let ((mty,mls,new_),l) =
                Lists.map_fold_left
                  (fun (mty,mls,new_) (ls,def) ->
                     let (vs, t) = open_ls_defn def in
                     let ((mty,new_,vss),vs) =
                       Lists.map_fold_left
                         (fun (mty,new_,vss) vs ->
                            let (mty,new_),ty = map (mty,new_) vs.vs_ty in
                            let vs' =
                              Term.create_vsymbol (Ident.id_clone vs.vs_name) ty
                            in
                            ((mty,new_,Mvs.add vs vs' vss),vs')
                         ) (mty,new_,Mvs.empty) vs
                     in
                     let (mty,mls,new_,t) = map_term mty mls vss new_ t in
                     let def = make_ls_defn ls vs t in
                     ((mty,mls,new_),def)
                  ) (mty,mls,new_) l
              in
              let d = create_logic_decl l in
              add_new mty mls new_ task_uc d
          | Dprop (k,pr,t) when not (keep_term t) ->
              let (mty,mls,new_,t) = map_term mty mls Mvs.empty [] t in
              let d = create_prop_decl k pr t in
              add_new mty mls new_ task_uc d
          | _ ->
              ((mty,mls), Task.add_decl task_uc d)
          end
      | _ -> ((mty,mls),Task.add_tdecl task_uc hd.Task.task_decl)
    )
    ((Mty.empty,Mls.empty), None)

let remove_ty_constr =
  (* TODO fix the pair *)
  Trans.bind (Trans.bind syntactic_transform remove_ty_constr)
    (fun (_, task) -> Trans.return task)

let () =
  Trans.register_transform "eliminate_unknown_ty_constr" remove_ty_constr
    ~desc:"Remove@ type@ unknown@ type@ constructor,@ could@ be@ used@ only@ after@ eliminating@ polymorphism."


let syntactic_transform_ls =
  Trans.on_meta Printer.meta_syntax_logic (fun metas ->
      let symbols = List.fold_left (fun acc meta_arg ->
      match meta_arg with
      | [MAls ls; MAstr _; MAint _] -> Sls.add ls acc
      | _ -> assert false) Sls.empty metas in
      Trans.return (fun ls -> Sls.mem ls symbols))

let remove_poly_unused_or_fail keep =
  let poly_ls ls =
    not (keep ls ||
         Stv.is_empty (Term.ls_ty_freevars ls))
  in
  Trans.decl (fun d ->
      begin match d.d_node with
        | Dparam l when poly_ls l ->
            []
        | Dlogic l when
            List.exists (fun (ls,_) -> poly_ls ls) l ->
            []
        | _ -> [d]
      end
    ) None

let remove_poly_unused_or_fail =
  (* TODO fix the pair *)
  Trans.bind syntactic_transform_ls remove_poly_unused_or_fail

let () =
  Trans.register_transform "eliminate_poly_unused_or_fail" remove_poly_unused_or_fail
    ~desc:"After elimination of polymorphism, remove last remnant."
