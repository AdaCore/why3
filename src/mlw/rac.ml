(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Ident
open Ty
open Ity
open Expr
open Term
open Pinterp_core
open Pretty
open Value

let debug_rac_check_sat =
  Debug.register_info_flag "rac:check_term_sat"
    ~desc:"satisfiability of terms in rac"
(* print debug information when checking the satisfiability of terms
   during rac *)

let debug_rac_check_term_result =
  Debug.register_info_flag "rac:check_term_result"
    ~desc:"print the result when terms are checked for validity"

type oracle_quant_var = env -> Term.vsymbol -> Value.value option

let oracle_quant_var_dummy _ _ = None

let warn_model_not_checked =
  Loc.register_warning "model_not_checked" "Warn that the model for a quantified variable has not been checked"

(* Get the value of a vsymbol with env.rac.get_value or a default value *)
let oracle_quant_var
    ?(bind_univ_quant_vars=false) ?(bind_univ_quant_vars_default=false)
    (oracle: oracle) : oracle_quant_var =
  fun env vs ->
  match vs.vs_name.id_loc with
  | None -> None
  | Some loc ->
      let value =
        if bind_univ_quant_vars then
          let check _ _ =
            Loc.warning warn_model_not_checked "Model value for all-quantified variable not checked" in
          oracle.for_variable env ~check ~loc:(Some loc) vs.vs_name (ity_of_ty vs.vs_ty)
        else None in
      let value =
        if value <> None then value else
        if bind_univ_quant_vars_default then
          Some (Pinterp_core.default_value_of_type env (ity_of_ty vs.vs_ty))
        else None in
      Option.iter (fun v ->
          register_used_value env (Some loc) vs.vs_name v) value;
      value

(******************************************************************************)
(*                                TERM TO TASK                                *)
(******************************************************************************)

(* Add declarations for additional term bindings in [vsenv] *)
let bind_term (vs, t) (task, ls_mt, ls_mv) =
  let ty = Option.get t.t_ty in
  let ls = create_fsymbol (id_clone vs.vs_name) [] ty in
  let ls_mt = ty_match ls_mt vs.vs_ty ty in
  let ls_mv = Mvs.add vs (fs_app ls [] ty) ls_mv in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

(* Add declarations for value bindings in [env.vsenv] *)
let bind_value env vs v (task, ls_mt, ls_mv) =
  let ty, ty_mt, ls_mt =
    (* [ty_mt] is a type substitution for [v],
       [ls_mt] is a type substitution for the remaining task *)
    if ty_closed v.v_ty then
      v.v_ty, Mtv.empty, ty_match ls_mt vs.vs_ty v.v_ty
    else
      ty_inst ls_mt vs.vs_ty, ty_match Mtv.empty v.v_ty vs.vs_ty, ls_mt in
  let ls = create_fsymbol (id_clone vs.vs_name) [] ty in
  let ls_mv = Mvs.add vs (fs_app ls [] ty) ls_mv in
  let vsenv, t = term_of_value ~ty_mt env [] v in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

(* Create and open a formula `p t` where `p` refers to a predicate without definition, to
   use the reduction engine to evaluate `t` *)
let undef_pred_decl, undef_pred_app, undef_pred_app_arg =
  let ls = let tv = create_tvsymbol (id_fresh "a") in
    create_psymbol (id_fresh "p") [ty_var tv] in
  let decl = Decl.create_param_decl ls in
  let app t = t_app ls [t] None in
  let app_arg t = match t with
    | {t_node= Tapp (ls, [t])} when ls_equal ls ls -> t
    | _ -> failwith "open_app" in
  decl, app, app_arg

(* Add declarations from local functions in [env.funenv] *)
let bind_fun rs (cexp, _) (task, ls_mv) =
  try
    let t = match cexp.c_node with
      | Cfun e -> Opt.get_exn Exit (term_of_expr ~prop:false e)
      | _ -> raise Exit in
    let ty_args = List.map (fun pv -> ty_of_ity pv.pv_ity) rs.rs_cty.cty_args in
    let ty_res = ty_of_ity rs.rs_cty.cty_result in
    let ls, ls_mv = match rs.rs_logic with
      | RLlemma | RLnone -> raise Exit
      | RLls ls -> ls, ls_mv
      | RLpv {pv_vs= vs} ->
          let ls = create_fsymbol (id_clone rs.rs_name) ty_args ty_res in
          let vss = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
          let ts = List.map t_var vss in
          let t0 = fs_app ls ts ty_res in
          let t = t_lambda vss [] t0 in
          let ls_mv = Mvs.add vs t ls_mv in
          ls, ls_mv in
    let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
    let decl = Decl.make_ls_defn ls vs_args t in
    let task = Task.add_logic_decl task [decl] in
    task, ls_mv
  with Exit -> task, ls_mv

let task_of_term ?(vsenv=[]) metas (env: env) t =
  let open Task in let open Decl in
  let free_sls = t_app_fold (fun sls ls _ _ -> Sls.add ls sls) Sls.empty t in
  let lsenv =
    let aux rs v mls =
      match rs.rs_logic with
      | RLls ls when Sls.mem ls free_sls -> Mls.add ls v mls
      | _ -> mls in
    Mrs.fold aux env.rsenv Mls.empty in
  (* Add to lsenv the logical symbols from env.lsenv that are in free_sls *)
  let lsenv =
    let aux ls v mls = if Sls.mem ls free_sls then Mls.add ls v mls else mls in
    Mls.fold aux env.lsenv lsenv in
  let add_used task td =
    let open Theory in
    match td.td_node with
    | Use th ->
        (* Format.eprintf "Rac.add_used Use %s@." th.th_name.id_string; *)
        Task.use_export task th
    | Clone (th, sm) ->
        (* FIXME: this clone cannot be correct, the substitution cannot be done like this *)
        (* Format.eprintf "Rac.add_used Clone %s@." th.th_name.id_string; *)
        (* Format.eprintf "tdecl = %a@." Pretty.print_tdecl td; *)
        let inst_df = Decl.Paxiom in
        let inst_pr = Decl.Mpr.map (fun _ -> Decl.Paxiom) sm.sm_pr in
        let inst_ts =
          Ty.Mts.fold (fun ts v acc ->
            if ts.ts_def = NoDef then Ty.Mts.add ts v acc else acc)
            sm.sm_ts Ty.Mts.empty
        in
        let inst_ls =
          Mls.fold (fun ls v acc ->
              let do_add = match task with
                | None -> false
                | Some task_hd -> Mid.mem v.Term.ls_name task_hd.task_known
              in
              if do_add then Mls.add ls v acc else acc)
            sm.sm_ls Mls.empty in
        let inst =
          {inst_df; inst_pr; inst_ty= sm.sm_ty; inst_ts; inst_ls } in
        Task.clone_export task th inst
    | _ -> task in
  let add_known _ decl (task, ls_mt, ls_mv) =
    match decl.d_node with
    | Dparam ls when Mls.contains lsenv ls ->
        (* Take value from lsenv (i.e. env.rsenv and env.lsenv) for declaration *)
        let vsenv, t = term_of_value env [] (Lazy.force (Mls.find ls lsenv)) in
        let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
        let t = t_ty_subst ls_mt ls_mv t in
        let ldecl = match ls.ls_args with
          | [] -> Decl.make_ls_defn ls [] t
          | _ ->
            begin match t_open_lambda t with
              | [], _, _ -> assert false
              | vsl, _, t' -> Decl.make_ls_defn ls vsl t'
            end
        in
        let decl = create_logic_decl [ldecl] in
        let task = add_decl task decl in
        task, ls_mt, ls_mv
    | Dprop (Plemma, prs, t) ->
        add_decl task (create_prop_decl Paxiom prs t), ls_mt, ls_mv
    | Dprop (Pgoal, _, _) -> task, ls_mt, ls_mv
    | _ -> add_decl task decl, ls_mt, ls_mv in
  let add_prog_const rs v (task, ls_mt, ls_mv) =
    let is_undefined_constant ls =
      let th_known = env.pmodule.Pmodule.mod_theory.Theory.th_known in
      match Mid.find ls.ls_name th_known with
      | Decl.{d_node = Dparam _} -> true
      | _ -> false in
    match rs.rs_logic with
    | Expr.RLls ls when is_undefined_constant ls ->
        let pr = create_prsymbol (id_fresh (asprintf "def_%a" print_rs rs)) in
        let vsenv, t = term_of_value env [] (Lazy.force v) in
        let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
        let t = t_equ (t_app ls [] ls.ls_value) t in
        let task = add_prop_decl task Paxiom pr t in
        task, ls_mt, ls_mv
    | _ -> task, ls_mt, ls_mv in
  let add_premise task t =
    let pr = create_prsymbol (id_fresh "premise") in
    Task.add_prop_decl task Decl.Paxiom pr t in
  (* building the task from scratch *)
  let task, ls_mt, ls_mv = None, Mtv.empty, Mvs.empty in
  (* adds the theories used and cloned from the enclosing module *)
  let th = env.pmodule.Pmodule.mod_theory in
  let task = List.fold_left add_used task th.Theory.th_decls in
  (* adds the local symbols used (??) *)
  let used = Task.used_symbols (Task.used_theories task) in
  let known_local = Mid.filter (fun id _ -> not (Mid.mem id used)) th.Theory.th_known in
  let task, ls_mt, ls_mv = Mid.fold add_known known_local (task, ls_mt, ls_mv) in
  (* adds the global program variables *)
  let task, ls_mt, ls_mv = Mrs.fold add_prog_const env.rsenv (task, ls_mt, ls_mv) in
  (* adds the logic functions from the model (??) *)
  let task, ls_mv = Mrs.fold bind_fun env.funenv (task, ls_mv) in
  (* adds the logic variables from the model (??) *)
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let task, ls_mt, ls_mv = Mvs.fold (bind_value env) env.vsenv (task, ls_mt, ls_mv) in
  (* adds the premises from the model (??) *)
  let task = fold_premises add_premise env.premises task in
  let t = t_ty_subst ls_mt ls_mv t in
  let task = List.fold_left (fun t (m, a) -> Task.add_meta t m a) task metas in
  (* adds the term to check as a goal *)
  let task =
    if t.t_ty = None then (* Add a formula as goal directly ... *)
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs t
    else (* ... and wrap a non-formula in a call to a predicate with no definition *)
      (* FIXME: does this case really used? what for? *)
      let task = add_decl task undef_pred_decl in
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs (undef_pred_app t) in
  task, ls_mv

(******************************************************************************)
(*                                DEFAULT RAC                                 *)
(******************************************************************************)

module Why = struct

  type why_prover = {
    command: string;
    driver: Driver.driver;
    limit: Call_provers.resource_limit;
  }

  let mk_why_prover ~command driver limit =
    {command; driver; limit}

  type config = {
    metas             : (Theory.meta * Theory.meta_arg list) list;
    trans             : Task.task Trans.tlist option;
    why_prover        : why_prover option;
    oracle_quant_var  : oracle_quant_var;
    elim_eps          : Task.task Trans.trans;
    main_config       : Whyconf.main;
  }

  let mk_config ?(metas=[]) ?trans ?why_prover ?(oracle_quant_var=oracle_quant_var_dummy) ~elim_eps whyconfig =
    let main_config = Whyconf.get_main whyconfig in
    {metas; trans; why_prover; oracle_quant_var; elim_eps; main_config}

  let mk_meta_lit (meta, s) =
    let open Theory in
    let meta = lookup_meta meta in
    let args = match meta.meta_type, s with
      | [MTstring], Some s -> [MAstr s]
      | [MTint], Some s -> [MAint (int_of_string s)]
      | [], None -> []
      | _ -> failwith "meta argument not implemented" in
    meta, args

  let mk_trans_lit env s = Trans.lookup_transform_l s env

  let mk_config_lit config env ?(metas=[]) ?trans ?why_prover:why_prover_lit ?oracle_quant_var () =
    let metas = List.map mk_meta_lit metas in
    let trans = Option.map (mk_trans_lit env) trans in
    let why_prover =
      let aux prover_string =
        let name, limit_time, limit_mem =
          match Strings.split ' ' prover_string with
          | [name; limit_time; limit_mem] ->
              name, float_of_string limit_time, int_of_string limit_mem
          | [name; limit_time] ->
              name, float_of_string limit_time, 1000
          | [name] -> name, 1., 1000
          | _ -> failwith "RAC reduce prover config must have format <prover>[ <time limit>[ <mem limit>]]" in
        let pr = Whyconf.filter_one_prover config (Whyconf.parse_filter_prover name) in
        let command = String.concat " " (pr.Whyconf.command :: pr.Whyconf.extra_options) in
        let driver = Driver.load_driver_for_prover (Whyconf.get_main config) env pr in
        let limit = Call_provers.{empty_limit with limit_time; limit_mem} in
        mk_why_prover ~command driver limit in
      Option.map aux why_prover_lit in
    let elim_eps = Trans.lookup_transform "eliminate_epsilon" env in
    mk_config ~metas ?trans ?why_prover ?oracle_quant_var ~elim_eps config

  (******************************************************************************)
  (*                                CHECK TERM                                  *)
  (******************************************************************************)

  (** When the task goal is [forall vs* . t], add declarations to the
      task that bind the variables [vs*] to concrete values (with
      env.config.oracle or default values), and make [t] the new goal. *)
  let bind_univ_quant_vars get_quant_value env task =
    try match (Task.task_goal_fmla task).t_node with
      | Tquant (Tforall, tq) ->
          let vs, _, t = t_open_quant tq in
          let values = List.map (fun vs -> Opt.get_exn Exit (get_quant_value env vs)) vs in
          let _, task = Task.task_separate_goal task in
          let task, ls_mt, ls_mv = List.fold_right2 (bind_value env) vs values (task, Mtv.empty, Mvs.empty) in
          let prs = Decl.create_prsymbol (id_fresh "goal") in
          let t = t_ty_subst ls_mt ls_mv t in
          Task.add_prop_decl task Decl.Pgoal prs t
      | _ -> raise Exit
    with Exit -> task

  let task_hd_equal t1 t2 = let open Task in let open Theory in let open Decl in
    (* Task.task_hd_equal is too strict: it requires physical equality between
       {t1,t2}.task_prev *)
    match t1.task_decl.td_node, t2.task_decl.td_node with
    | Decl {d_node = Dprop (Pgoal,p1,g1)}, Decl {d_node = Dprop (Pgoal,p2,g2)} ->
        pr_equal p1 p2 && t_equal_strict g1 g2
    | _ -> t1 == t2

  (** Apply the (reduction) transformation and fill universally quantified
      variables in the head of the task by values obtained with
      env.config.oracle, recursively. *)
  let rec trans_and_bind_quants get_quant_value env trans task =
    let task = bind_univ_quant_vars get_quant_value env task in
    let tasks = Trans.apply trans task in
    let task_unchanged = match tasks with
      | [task'] -> Option.equal task_hd_equal task' task
      | _ -> false in
    if task_unchanged then
      tasks
    else
      List.flatten (List.map (trans_and_bind_quants get_quant_value env trans) tasks)

  (** Compute the value of a term by using the (reduction) transformation *)
  let mk_compute_term ?(metas=[]) ?trans ?oracle_quant_var () env t =
    match trans with
    | None -> t
    | Some trans ->
        let task, ls_mv = task_of_term metas env t in
        if t.t_ty = None then (* [t] is a formula *)
          let oracle_quant_var = Option.value ~default:oracle_quant_var_dummy oracle_quant_var in
          let tasks = trans_and_bind_quants oracle_quant_var env trans task in
          match List.map Task.task_goal_fmla tasks with
          | [] -> t_true
          | t :: ts -> List.fold_left t_and t ts
        else (* [t] is not a formula *)
          let t = match Trans.apply trans task with
            | [task] -> undef_pred_app_arg (Task.task_goal_fmla task)
            | _ -> failwith "compute_term" in
          (* Free vsymbols in the original [t] have been substituted in by fresh
             lsymbols (actually: ls @ []) to bind them to declarations in the
             task. Now we have to reverse these substitution to ensures that the
             reduced term is valid in the original environment of [t]. *)
          let reverse vs t' t =
            if t_occurs t' t then t_replace t' (t_var vs) t else t in
          Mvs.fold reverse ls_mv t

  let mk_compute_term_lit env ?metas ?(trans="compute_in_goal") ?oracle_quant_var =
    let metas = Option.map (List.map mk_meta_lit) metas in
    let trans = mk_trans_lit env trans in
    mk_compute_term ?metas ~trans ?oracle_quant_var

  (** Check the validiy of a term that has been encoded in a task by the (reduction) transformation *)
  let check_term_compute oracle env trans task =
    let is_false = function
      | Some {Task.task_decl= Theory.{
          td_node= Decl Decl.{
              d_node= Dprop (Pgoal, _, {t_node= Tfalse})}}} ->
          true
      | _ -> false in
    match trans_and_bind_quants oracle env trans task with
    | [] -> Some true
    | tasks ->
        Debug.dprintf debug_rac_check_sat "Transformation produced %d tasks@." (List.length tasks);
        if List.exists is_false tasks then
          Some false
        else (
          List.iter (Debug.dprintf debug_rac_check_sat "- %a@." print_tdecl)
            (List.filter_map (Option.map (fun t -> t.Task.task_decl)) tasks);
          None )

  (** Check the validiy of a term that has been encoded in a task by dispatching it to a prover *)
  let check_term_dispatch {command; driver; limit} cnf task =
    let open Call_provers in
    let call =
      Driver.prove_task
        ~command ~config:cnf.main_config
        ~limit driver task
    in
    let res = wait_on_call call in
    Debug.Stats.add_timing "rac_prover" res.pr_time;
    Debug.dprintf debug_rac_check_sat "@[<h>Check term dispatch answer: %a@]@."
      print_prover_answer res.pr_answer;
    match res.pr_answer with
    | Valid -> Some true
    | Invalid -> Some false
    | _ -> None

  let negate_goal task =
    let open Task in
    let tdecl, task = task_separate_goal task in
    match tdecl.Theory.td_node with
    | Theory.Decl Decl.{d_node= Dprop (Pgoal,p,t)} ->
        add_prop_decl task Decl.Pgoal p (t_not t)
    | _ -> failwith "negate_goal"

  let check_term_dispatch ~try_negate rp cnf task =
    match check_term_dispatch rp cnf task with
    | None when try_negate ->
        Debug.dprintf debug_rac_check_sat "Try negation.@.";
        let task = negate_goal task in
        let res = check_term_dispatch rp cnf task in
        Option.map (fun b -> not b) res
    | r -> r

  (* Replace (sub-)terms marked by {!Ident.has_rac_assume} by [t_true]. *)
  let assumed_conjuncts t =
    let assumed = ref [] in
    let rec loop t =
      if Ident.has_rac_assume t.t_attrs then
        assumed := t :: !assumed
      else match t.t_node with
        | Tbinop _ -> t_iter loop t
        | _ -> () in
    loop t; !assumed

  (* The callee must ensure that RAC is enabled. *)
  let check_term cnf : check_term =
    fun ?vsenv ctx t ->
    Debug.dprintf debug_rac_check_sat "@[<hv2>Check term: %a %a@]@." print_term t
      Pp.(print_list space (fun fmt vs -> fprintf fmt "@[%a=%a@]" print_vs vs print_value (get_vs ctx.cntr_env vs)))
      (Mvs.keys (t_freevars Mvs.empty t)) ;
    let task, _ = task_of_term ?vsenv cnf.metas ctx.cntr_env t in
    let task =
      let g, task' = Task.task_separate_goal task in
      let t = match g with
        | Theory.{td_node= Decl Decl.{d_node= Dprop (Pgoal, _, t)}} -> t
        | _ -> assert false in
      let assumptions = assumed_conjuncts t in
      if assumptions = [] then task
      else
        let for_assumption task t =
          let pid = Ident.id_fresh "rac'assume" in
          Task.add_prop_decl task Decl.Paxiom (Decl.create_prsymbol pid) t in
        let task' = List.fold_left for_assumption task' assumptions in
        Task.add_tdecl task' g in
    let res = (* Try checking the term using computation first ... *)
      Option.map (fun b -> Debug.dprintf debug_rac_check_sat "Computed %b.@." b; b)
        (Option.bind cnf.trans
           (fun trans ->
              check_term_compute cnf.oracle_quant_var ctx.cntr_env trans task))
    in
    let res =
      if res = None then (* ... then try solving using a prover *)
        Option.map (fun b -> Debug.dprintf debug_rac_check_sat "Dispatched: %b.@." b; b)
          (Option.bind cnf.why_prover
             (fun rp ->
               check_term_dispatch ~try_negate:true rp cnf task))
      else res in
    let task_filename = match Sys.getenv_opt "WHY3RACTASKDIR" with
      | Some temp_dir when Debug.test_flag debug_rac_check_term_result ->
          let task = Trans.apply cnf.elim_eps task in
          let filename = Filename.temp_file ~temp_dir "gnatwhy3-task" ".why" in
          let out = open_out filename in
          fprintf (formatter_of_out_channel out) "%a@." Pretty.print_task task;
          close_out out;
          Some filename
      | _ -> None in
    let pp_task_filename fmt = if task_filename <> None then
        fprintf fmt " (%s)" (Option.get task_filename) in
    match res with
    | Some true ->
        Debug.dprintf debug_rac_check_term_result "%a%t@."
          report_cntr_head (ctx, "is ok", t) pp_task_filename
    | Some false ->
        Debug.dprintf debug_rac_check_term_result "%a%t@."
          report_cntr (ctx, "failed", t) pp_task_filename;
        raise (Fail (ctx, t))
    | None ->
        let msg = "cannot be evaluated" in
        Debug.dprintf debug_rac_check_term_result "%a%t@."
          report_cntr_head (ctx, msg, t) pp_task_filename;
        let reason = asprintf "%a" report_cntr_title (ctx, msg) in
        raise (Cannot_decide (ctx, [t], reason))

  let mk_check_term
        ?metas ?trans ?why_prover ?oracle_quant_var ~config ~elim_eps () =
    check_term (mk_config ?metas ?trans ?why_prover ?oracle_quant_var ~elim_eps config)

  let mk_check_term_lit cnf env ?metas ?(trans="compute_in_goal") ?why_prover ?oracle_quant_var () =
    check_term (mk_config_lit cnf env ?metas ~trans ?why_prover ?oracle_quant_var ())
end
