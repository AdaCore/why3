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
      Trans.return (fun ts -> Sts.exists (ts_equal ts) symbols))

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

  Trans.fold_decl (fun d (already_removed, task_uc) ->
      match d.d_node with
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
      | _ -> (already_removed, Task.add_decl task_uc d))
    (Sls.empty, None)

let remove_types =
  (* TODO fix the pair *)
  Trans.bind (Trans.bind syntactic_transform remove_terms)
    (fun (_, task) -> Trans.return task)

let () =
  Trans.register_transform "eliminate_unknown_types" remove_types
    ~desc:"Remove@ types@ unknown@ to@ the@ prover@ and@ terms@ referring@ to@ them@."
