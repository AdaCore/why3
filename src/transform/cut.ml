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
open Ty
open Generic_arg_trans_utils
open Args_wrapper

(** This file contains transformations with arguments that adds/removes
    declarations from the context *)

(* Explanation for assert and cut *)
let assert_expl = "asserted formula"

(* From task [delta |- G] , build the tasks [delta, t | - G] and [delta] |- t] *)
let cut t name =
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
  Trans.par [goal; goal_cut]


(* From task [delta |- G] , build the tasks [delta] |- t] and [delta, t | - G] *)
let assert_tac t name =
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
  Trans.par [goal_cut; goal]

(* from task [delta, name1, name2, ... namen |- G] build the task [delta |- G] *)
let remove_list name_list =
  Trans.decl
    (fun d ->
      match d.d_node with
      | Dprop (k, pr, _) when
          (k != Pgoal &&
            List.exists
             (fun x -> match x with
                       | Tsprsymbol x -> Ident.id_equal pr.pr_name x.pr_name
                       | _ -> false
             )
             name_list) ->
        []
      | Dparam ls when
          (List.exists
             (fun x -> match x with
                       | Tslsymbol x -> Ident.id_equal ls.ls_name x.ls_name
                       | _ -> false
             )
             name_list) ->
       []
      | Dlogic dl when
        (* also remove all dependant recursive declarations (as expected) *)
          List.exists
          (fun (ls, _) -> List.exists
             (fun x -> match x with
                       | Tslsymbol x -> Ident.id_equal ls.ls_name x.ls_name
                       | _ -> false
             )
             name_list)
            dl ->
       []
      | Dind il when
        (* also remove all dependant inductive declarations (as expected) *)
          List.exists
          (fun (ls, _) -> List.exists
             (fun x -> match x with
                       | Tslsymbol x -> Ident.id_equal ls.ls_name x.ls_name
                       | _ -> false
             )
             name_list)
            (snd il) ->
       []
      | Dtype ty when
          (List.exists
             (fun x -> match x with
                       | Tstysymbol x -> Ident.id_equal ty.ts_name x.ts_name
                       | _ -> false
             )
             name_list) ->
        []
      | Ddata tyl when
          (* also remove all dependant recursive declarations (as expected) *)
          List.exists
          (fun (ty, _) -> List.exists
             (fun x -> match x with
                       | Tstysymbol x -> Ident.id_equal ty.ts_name x.ts_name
                       | _ -> false
             )
             name_list)
            tyl ->
       []
      | _ -> [d])
    None

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
  let replace_all hyp new_constant ls_term =
    Trans.decl (fun d ->
      match d.d_node with
      | _ when (Decl.d_equal d hyp || Decl.d_equal d new_constant) -> [d]
      | Dprop (p, pr, t1) ->
        let new_decl = create_prop_decl p pr (replace_in_term t ls_term t1) in
        [new_decl]
      | _ -> [d]) None
  in
  Trans.bind_comp (pose clear name t)
     (fun (hyp,new_constant,ls_term) -> replace_all hyp new_constant ls_term)

let () = wrap_and_register ~desc:"clear all axioms but the hypothesis argument"
    "clear_but"
    (Tprlist Ttrans) clear_but

let () = wrap_and_register
    ~desc:"cut <term> [name] makes a cut with hypothesis 'name: term'"
    "cut"
    (Tformula (Topt ("as",Tstring Ttrans_l))) cut

let () = wrap_and_register
    ~desc:"cut <term> [name] makes an assert with hypothesis 'name: term'"
    "assert"
    (Tformula (Topt ("as",Tstring Ttrans_l))) assert_tac

let () = wrap_and_register
    ~desc:"remove <prop list>: removes a list of hypothesis given by their names separated with ','. Example: remove_list a,b,c "
     "remove"
     (Tlist Ttrans) (fun l -> remove_list l)

let () = wrap_and_register
    ~desc:"use_th <theory> imports the theory" "use_th"
    (Ttheory Ttrans) use_th

let pose (name: string) (t: term) =
  Trans.bind (pose false name t) (fun (_, task) -> Trans.store (fun _ -> task))

let () = wrap_and_register
    ~desc:"pose <name> <term> adds a new constant <name> equal to <term>"
    "pose"
    (Tstring (Tterm Ttrans)) pose

let () = wrap_and_register
    ~desc:"hide <name> <term> adds a new constant <name> equal to <term> and replace everywhere the term with the new constant."
    "hide"
    (Tstring (Tterm Ttrans)) (hide false)

let () = wrap_and_register
    ~desc:"hide and clear <name> <term> adds a new constant <name> which replaces all occurences of <term>."
    "hide_and_clear"
    (Tstring (Tterm Ttrans)) (hide true)
