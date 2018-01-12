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
open Task
open Theory
open Reduction_engine

let meta_rewrite = Theory.register_meta "rewrite" [Theory.MTprsymbol]
  ~desc:"Declares@ the@ given@ proposition@ as@ a@ rewrite@ rule."

let meta_rewrite_def = Theory.register_meta "rewrite_def" [Theory.MTlsymbol]
  ~desc:"Declares@ the@ definition@ of@ the@ symbol@ as@ a@ rewrite@ rule."

let meta_compute_max_steps = Theory.register_meta_excl "compute_max_steps"
  [Theory.MTint]
  ~desc:"Maximal@ number@ of@ reduction@ steps@ done@ by@ compute@ \
         transformation"

let compute_max_steps = ref 1024

(* not yet used
let meta_begin_compute_context =
  Theory.register_meta "begin_compute_context" []
    ~desc:"Marks@ the@ position@ where@ computations@ are@ done@ by@ \
           transformation@ 'compute_in_context'."
*)

let rule_label = Ident.create_label "rewrite"

let collect_rules p env km prs t =
  let acc = Task.task_fold
    (fun acc td -> match td.Theory.td_node with
      | Theory.Decl { d_node = Dprop((Plemma|Paxiom), pr, t) }
        when Decl.Spr.mem pr prs ||
           Ident.Slab.mem rule_label pr.pr_name.Ident.id_label ||
             Ident.Slab.mem rule_label t.t_label ->
          (pr,t) :: acc
      | _ -> acc)
    [] t
  in
  List.fold_left
    (fun e (pr,t) ->
      try add_rule t e
      with NotARewriteRule msg ->
        Warning.emit "proposition %a cannot be turned into a rewrite rule: %s"
         Pretty.print_pr pr msg;
        e
    )
    (create p env km) acc

let normalize_goal p env (prs : Decl.Spr.t) task =
  match task with
  | Some
      { task_decl =
          { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
        task_prev = prev;
        task_known = km;
      } ->
    let engine = collect_rules p env km prs task in
    let f = normalize ~limit:!compute_max_steps engine f in
    begin match f.t_node with
    | Ttrue -> []
    | _ ->
      let d = Decl.create_prop_decl Pgoal pr f in
      [Task.add_decl prev d]
    end
  | _ -> assert false


let normalize_goal_transf p env : 'a Trans.trans =
  let tr : 'a Trans.trans =
    Trans.on_tagged_pr meta_rewrite
      (fun prs -> if p.compute_defs
        then Trans.store (normalize_goal p env prs)
        else Trans.on_tagged_ls meta_rewrite_def
          (fun lss -> let p = { p with compute_def_set = lss } in
                      Trans.store (normalize_goal p env prs)
          ))
  in
  Trans.on_meta_excl meta_compute_max_steps
    (function
      | None -> tr
      | Some [Theory.MAint n] -> compute_max_steps := n; tr
      | _ ->  assert false)


let normalize_goal_transf_all env =
  let p = { compute_defs = true;
            compute_builtin = true;
            compute_def_set = Term.Mls.empty;
          } in
  normalize_goal_transf p env

let normalize_goal_transf_few env =
  let p = { compute_defs = false;
            compute_builtin = true;
            compute_def_set = Term.Mls.empty;
          } in
  normalize_goal_transf p env

let () =
  Trans.register_env_transform_l "compute_in_goal" normalize_goal_transf_all
  ~desc:"Performs@ possible@ computations@ in@ goal, including@ by@ \
         declared@ rewrite@ rules"

let () =
  Trans.register_env_transform_l "compute_specified" normalize_goal_transf_few
  ~desc:"Rewrite@ goal@ using@ specified@ rules"
