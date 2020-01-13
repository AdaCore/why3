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
open Ty
open Generic_arg_trans_utils
open Args_wrapper

(** This file contains transformations with arguments that adds/removes
    declarations from the context *)

(* Explanation for assert and cut *)
let assert_expl = "asserted formula"

let assert_aux ~is_cut t name =
  let name =
    match name with
    | Some name -> name
    | None -> "h"
  in
  let h = Decl.create_prsymbol (gen_ident name) in
  let g_t = create_goal ~expl:assert_expl h t in
  let h_t = Decl.create_prop_decl Decl.Paxiom h t in
  let goal_cut = Trans.goal (fun _ _ -> [g_t]) in
  let goal = Trans.add_decls [h_t] in
  if is_cut then
    Trans.par [goal; goal_cut]
  else
    Trans.par [goal_cut; goal]

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut t name =
  assert_aux ~is_cut:true t name

(* From task [delta |- G] , build the tasks [delta] |- t] and [delta, t | - G] *)
let assert_tac t name =
  assert_aux ~is_cut:false t name

let get_ident_symbol s =
  match s with
  | Tstysymbol ty -> ty.ts_name
  | Tsprsymbol pr -> pr.pr_name
  | Tslsymbol ls -> ls.ls_name

(* from task [delta, name1, name2, ... namen |- G] build the task [delta |- G] *)
let remove_list ~is_rec (name_list: symbol list) =
    Trans.fold_map (fun td (removed_ids, task_uc) ->
      match td.Task.task_decl.Theory.td_node with
      | Theory.Use _ | Theory.Clone _ | Theory.Meta _ ->
          (removed_ids, Task.add_tdecl task_uc td.Task.task_decl)
      | Theory.Decl d ->
          let removed_in_decls = Ident.Sid.inter removed_ids (get_decl_syms d) in
          begin match d.d_node with
            | Dprop (Pgoal, _, _) ->
               begin try
                   (removed_ids, Task.add_decl task_uc d)
                 with Decl.UnknownIdent id -> raise (Remove_unknown (d, id))
               end
            | _ when Ident.Sid.exists (fun x -> Ident.Sid.mem x d.d_news) removed_ids ->
                (* The task create an element we want to delete -> removal *)
                if is_rec then
                  (Ident.Sid.union removed_ids d.d_news, task_uc)
                else
                  (removed_ids, task_uc)
            | _ when not (Ident.Sid.is_empty removed_in_decls) ->
                (* The task create an element we want to add but it uses deleted
                   elements *)
                if is_rec then
                  (Ident.Sid.union removed_ids d.d_news, task_uc)
                else
                  raise (Remove_unknown (d, Ident.Sid.choose removed_in_decls))
            | _ ->
                (removed_ids, Task.add_decl task_uc d)
          end) (Ident.Sid.of_list (List.map get_ident_symbol name_list)) None

(* from task [delta, name1, name2, ... namen |- G] build the task [name1, name2, ... namen |- G] *)
let clear_but (l: prsymbol list) local_decls =
  Trans.decl
    (fun d ->
      match d.d_node with
      | Dprop (Paxiom, pr, _t) when List.mem pr l ->
        [d]
      | Dprop (Paxiom, _pr, _t) when List.exists (fun x -> Decl.d_equal x d) local_decls ->
        []
      | _ -> [d]) None

let clear_but (l: prsymbol list) =
  Trans.bind get_local (clear_but l)

let use_th th =
  Trans.store Task.(function
  | Some { task_decl = { Theory.td_node = Theory.Decl d }; task_prev = prev } ->
      add_decl (use_export prev th) d
  | _ -> assert false)
  (*Trans.add_tdecls [Theory.create_use th]*)

(* Equivalent of Coq pose (x := term). Adds a new constant of appropriate type
   and an hypothesis x = term.
   This function returns the declarations of hypothesis and constant. *)
let pose (clear: bool) (name: string) (t: term) =
  let ty = Term.t_type t in
  let ls = Term.create_lsymbol (gen_ident name) [] (Some ty) in
  let ls_term = Term.t_app_infer ls [] in
  let new_constant = Decl.create_param_decl ls in
  let pr = create_prsymbol (gen_ident "H") in
  (* hyp = [pr : ls = t] *)
  let hyp =
    Decl.create_prop_decl Paxiom pr (Term.t_app_infer ps_equ [ls_term;t])
  in
  let trans_new_task =
    if clear then
      Trans.add_decls [new_constant]
    else
      Trans.add_decls [new_constant; hyp]
  in
  (* Note that sort is necessary *and* the complexity is probably the same as if
     we use a function Trans.prepend_decl (which will be linear in the size of
     the task. Sort should be too). *)
  Trans.compose trans_new_task
    (Trans.compose sort (Trans.store (fun task -> ((hyp, new_constant, ls_term), task))))

(* Sometimes it is useful to hide part of a term (actually to pose a constant
   equal to a term). It may also help provers to completely remove reference to
   stuff *)
let hide (clear: bool) (name: string) (t: term) =
  let add_decls list_decl task =
    List.fold_left (fun task d -> Task.add_decl task d) task list_decl in

  let replace_all hyp new_constant ls_term task =
    let (_, new_task) =
      let decls = Task.task_tdecls task in
      List.fold_left (fun (to_add, task_uc) td ->
          match td.Theory.td_node with
          | Theory.Decl {d_node = Dprop (Decl.Pgoal, pr, t1); _} ->
              (* Add declaration that depends on the rewriting of declaration
                 *after* the declaration of the new_constant *)
              let task_uc = add_decls to_add task_uc in
              let new_decl = create_prop_decl Decl.Pgoal pr (t_replace t ls_term t1) in
              let task_uc = Task.add_decl task_uc new_decl in
              ([], task_uc)
          | Theory.Decl d when (Decl.d_equal d hyp || Decl.d_equal d new_constant) ->
              (to_add, Task.add_tdecl task_uc td)
          | Theory.Decl ({d_node = Dprop (p, pr, t1); _} as d) ->
              let new_decl = create_prop_decl p pr (t_replace t ls_term t1) in
              if d_equal new_decl d then
                (to_add, Task.add_decl task_uc d)
              else
                (new_decl :: to_add, task_uc)
          | _ -> (to_add, Task.add_tdecl task_uc td)
        ) ([], None) decls in
    new_task in
  let replace_all hyp new_constant ls_term =
    Trans.store (replace_all hyp new_constant ls_term) in
  Trans.bind_comp (pose clear name t)
     (fun (hyp,new_constant,ls_term) -> replace_all hyp new_constant ls_term)

let () = wrap_and_register
    ~desc:"clear_but <name list>@ \
      clears@ all@ premises@ except@ the@ listed@ ones."
    "clear_but"
    (Tprlist Ttrans) clear_but

let () = wrap_and_register
    ~desc:"cut <term> [name]@ \
      makes@ a@ cut@ with@ a@ hypothesis@ 'name: term'."
    "cut"
    (Tformula (Topt ("as",Tstring Ttrans_l))) cut

let () = wrap_and_register
    ~desc:"assert <term> [name]@ \
      makes@ an@ assertion@ with@ a@ hypothesis@ 'name: term'."
    "assert"
    (Tformula (Topt ("as",Tstring Ttrans_l))) assert_tac

let () = wrap_and_register
    ~desc:"remove <name list>@ removes@ the@ listed@ premises."
     "remove"
    (Tlist Ttrans) (fun l -> remove_list ~is_rec:false l)

let () = wrap_and_register
    ~desc:"remove <name list>@ removes@ the@ listed@ premises@ and@ everything@ \
           depending@ on@ that."
     "remove_rec"
    (Tlist Ttrans) (fun l -> remove_list ~is_rec:true l)

let () = wrap_and_register
    ~desc:"use_th <theory>@ imports@ the@ given@ theory."
    "use_th"
    (Ttheory Ttrans) use_th

let pose (name: string) (t: term) =
  Trans.bind (pose false name t) (fun (_, task) -> Trans.store (fun _ -> task))

let () = wrap_and_register
    ~desc:"pose <name> <term>@ \
      adds@ a@ new@ constant@ <name>@ equal@ to@ <term>."
    "pose"
    (Tstring (Tterm Ttrans)) pose

let () = wrap_and_register
    ~desc:"hide <name> <term>@ \
      adds@ a@ new@ constant@ <name>@ equal@ to@ <term>@ \
      and@ replaces@ everywhere@ the@ term@ with@ the@ new@ constant."
    "hide"
    (Tstring (Tterm Ttrans)) (hide false)

let () = wrap_and_register
    ~desc:"hide_and_clear <name> <term>@ \
      adds@ a@ new constant@ <name>@ which@ replaces@ all@ \
      occurences@ of@ <term>."
    "hide_and_clear"
    (Tstring (Tterm Ttrans)) (hide true)
