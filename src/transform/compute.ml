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
open Reduction_engine
open Args_wrapper

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

let rule_attr = Ident.create_attribute "rewrite"

let collect_rules p env km prs t =
  let acc = Task.task_fold
    (fun acc td -> match td.Theory.td_node with
      | Theory.Decl { d_node = Dprop((Plemma|Paxiom), pr, t) }
        when Decl.Spr.mem pr prs ||
           Ident.Sattr.mem rule_attr pr.pr_name.Ident.id_attrs ||
             Ident.Sattr.mem rule_attr t.t_attrs ->
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

let normalize_hyp_or_goal ?pr_norm ?step_limit engine : Task.task Trans.tlist  =
  let step_limit =
    if step_limit = None then Some !compute_max_steps else step_limit
  in
  Trans.decl_l (fun d ->
    match d.d_node with
    | Dprop (Pgoal, pr, t) when pr_norm = None ->
        let t = normalize ?step_limit ~limit:!compute_max_steps engine t in
        begin match t.t_node with
        | Ttrue -> []
        | _ ->
            let d = Decl.create_prop_decl Pgoal pr t in
            [[d]]
        end
    | Dprop (k, pr, t) when Opt.fold (fun _ -> pr_equal pr) false pr_norm ->
      let t = normalize ?step_limit:step_limit ~limit:!compute_max_steps engine t in
      let d = Decl.create_prop_decl k pr t in
      [[d]]
    | _ -> [[d]]) None

let craft_engine p env prs task =
  let km = Task.task_known task in
  collect_rules p env km prs task

let collect_rules_trans p env : Reduction_engine.engine Trans.trans =
  Trans.on_tagged_pr meta_rewrite
    (fun prs -> if p.compute_defs
    then Trans.store (craft_engine p env prs)
    else Trans.on_tagged_ls meta_rewrite_def
        (fun lss -> let p = { p with compute_def_set = lss } in
        Trans.store (craft_engine p env prs)
        ))

let normalize_goal_transf ?pr_norm ?step_limit p env : 'a Trans.trans =
  let tr = collect_rules_trans p env in
  Trans.on_meta_excl meta_compute_max_steps
    (function
      | None ->
          Trans.bind tr (fun engine -> normalize_hyp_or_goal ?pr_norm ?step_limit engine)
      | Some [Theory.MAint n] -> compute_max_steps := n;
          Trans.bind tr (fun engine -> normalize_hyp_or_goal ?pr_norm ?step_limit engine)
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

let normalize_hyp step_limit pr_norm env =
  let p = { compute_defs = true;
            compute_builtin = true;
            compute_def_set = Term.Mls.empty;
          } in
  normalize_goal_transf ?pr_norm ?step_limit p env

let () = wrap_and_register ~desc:"experimental: Takes a prsymbol and reduce \
    one \"elementary\" step."
    "step"
    (Topt ("in", Tprsymbol Tenvtrans_l)) (normalize_hyp (Some 1))

let () = wrap_and_register ~desc:"experimental: Same as step except that it \
    reduces the given number of steps."
    "steps"
    (Tint (Topt ("in", Tprsymbol Tenvtrans_l))) (fun n -> normalize_hyp (Some n))


let () = wrap_and_register ~desc:"Performs@ possible@ computations@ in@ given \
    hypothesis@ including@ by@ declared@ rewrite@ rules"
    "compute_hyp"
    (Topt ("in", Tprsymbol Tenvtrans_l)) (normalize_hyp None)

let normalize_hyp_few step_limit pr_norm env =
  let p = { compute_defs = false;
            compute_builtin = true;
            compute_def_set = Term.Mls.empty;
          } in
  normalize_goal_transf ?pr_norm ?step_limit p env

let () = wrap_and_register ~desc:"Performs@ possible@ computations@ in@ given \
    hypothesis@ using@ specified@ rules"
    "compute_hyp_specified"
    (Topt ("in", Tprsymbol Tenvtrans_l)) (normalize_hyp_few None)
