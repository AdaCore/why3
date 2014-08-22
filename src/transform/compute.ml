(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

let meta = Theory.register_meta "rewrite" [Theory.MTprsymbol]
  ~desc:"Declares@ the@ given@ proposition@ as@ a@ rewrite@ rule."

let collect_rule_decl prs e d =
  match d.Decl.d_node with
    | Decl.Dtype _ | Decl.Ddata _ | Decl.Dparam _ | Decl.Dind  _
    | Decl.Dlogic _ -> e
    | Decl.Dprop(_, pr, t) ->
      if Decl.Spr.mem pr prs then
        try
          Reduction_engine.add_rule t e
        with Reduction_engine.NotARewriteRule msg ->
          Warning.emit "proposition %a cannot be turned into a rewrite rule: %s"
            Pretty.print_pr pr msg;
          e
      else e

let collect_rules env km prs t =
  Task.task_fold
    (fun e td -> match td.Theory.td_node with
      | Theory.Decl d -> collect_rule_decl prs e d
      | _ -> e)
    (Reduction_engine.create env km) t

let normalize_goal env (prs : Decl.Spr.t) task =
  match task with
  | Some
      { task_decl =
          { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
        task_prev = prev;
        task_known = km;
      } ->
    let engine = collect_rules env km prs task in
    let f = Reduction_engine.normalize engine f in
    begin match f.t_node with
    | Ttrue -> []
    | _ ->
      let d = Decl.create_prop_decl Pgoal pr f in
      [Task.add_decl prev d]
    end
  | _ -> assert false


let normalize_transf env =
  Trans.on_tagged_pr meta (fun prs -> Trans.store (normalize_goal env prs))

let () = Trans.register_env_transform_l "compute_in_goal" normalize_transf
  ~desc:"Normalize@ terms@ with@ respect@ to@ rewrite@ rules@ declared as metas"
