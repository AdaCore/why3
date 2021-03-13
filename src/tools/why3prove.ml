(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Wstdlib
open Whyconf
open Theory
open Task

let usage_msg =
  "Usage: [[<file>|-] [-T <theory> [-G <goal>]...]...]...\n\
   Run some transformation or prover on the given goals."

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []
(* Option for printing counterexamples with JSON formatting *)
let opt_json : [< `All | `Values ] option ref = ref None
let opt_check_ce_model = ref false
let opt_print_original_model = ref false
let opt_print_derived_model = ref false
let opt_rac_prover = ref None
let opt_rac_try_negate = ref false
let opt_ce_check_verbosity = ref None

let () = (* Instead of additional command line parameters *)
  if Opt.get_def "" (Sys.getenv_opt "WHY3PRINTORIGINALMODEL") = "yes" then
    opt_print_original_model := true;
  if Opt.get_def "" (Sys.getenv_opt "WHY3PRINTDERIVEDMODEL") = "yes" then
    opt_print_derived_model := true

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory x =
  let l = Strings.split '.' x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match !opt_input, p with
  | None, [] ->
      eprintf "Option '-T'/'--theory' with a non-qualified \
        argument requires an input file.@.";
      exit 1
  | Some tlist, [] ->
      let glist = Queue.create () in
      let elist = Queue.create () in
      Queue.push (x, p, t, glist, elist) tlist;
      opt_theory := Some glist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      let glist = Queue.create () in
      let elist = Queue.create () in
      Queue.push (x, p, t, glist,elist) tlist;
      opt_theory := Some glist

let add_opt_goal x =
  let glist = match !opt_theory, !opt_input with
    | None, None -> eprintf
        "Option '-G'/'--goal' requires an input file or a library theory.@.";
        exit 1
    | None, Some _ ->
        add_opt_theory "Top";
        Opt.get !opt_theory
    | Some glist, _ -> glist in
  let l = Strings.split '.' x in
  Queue.push (x, l) glist

let add_opt_trans x = opt_trans := x::!opt_trans

let add_opt_meta meta =
  let meta_name, meta_arg =
    try
      let index = String.index meta '=' in
      (String.sub meta 0 index),
      Some (String.sub meta (index+1) (String.length meta - (index + 1)))
    with Not_found ->
      meta, None
  in
  opt_metas := (meta_name,meta_arg)::!opt_metas

let opt_driver = ref []
let opt_parser = ref None
let opt_prover = ref None
let opt_output = ref None
let opt_timelimit = ref None
let opt_stepslimit = ref None
let opt_memlimit = ref None
let opt_command = ref None
let opt_task = ref None

let opt_print_theory = ref false
let opt_print_namespace = ref false

let option_list =
  let open Getopt in
  [ Key ('T', "theory"), Hnd1 (AString, add_opt_theory),
    "<theory> select <theory> in the input file or in the library";
    Key ('G', "goal"), Hnd1 (AString, add_opt_goal),
    "<goal> select <goal> in the last selected theory";
    Key ('P', "prover"), Hnd1 (AString, fun s -> opt_prover := Some s),
    "<prover> prove or print (with -o) the selected goals";
    Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    Key ('t', "timelimit"), Hnd1 (AInt, fun i -> opt_timelimit := Some i),
    "<sec> set the prover's time limit (default=10, no limit=0)";
    Key ('s', "stepslimit"), Hnd1 (AInt, fun i -> opt_stepslimit := Some i),
    "<steps> set the prover's step limit (default: no limit)";
    Key ('m', "memlimit"), Hnd1 (AInt, fun i -> opt_memlimit := Some i),
    "<MiB> set the prover's memory limit (default: no limit)";
    Key ('a', "apply-transform"), Hnd1 (AString, add_opt_trans),
    "<transf> apply a transformation to every task";
    Key ('M', "meta"), Hnd1 (AString, add_opt_meta),
    "<meta>[=<string>] add a meta to every task";
    Key ('D', "driver"), Hnd1 (AString, fun s -> opt_driver := s::!opt_driver),
    "<file> specify a prover's driver (conflicts with -P)";
    Key ('o', "output"), Hnd1 (AString, fun s -> opt_output := Some s),
    "<dir> print the selected goals to separate files in <dir>";
    KLong "print-theory", Hnd0 (fun () -> opt_print_theory := true),
    " print selected theories";
    KLong "print-namespace", Hnd0 (fun () -> opt_print_namespace := true),
    " print namespaces of selected theories";
    Debug.Args.desc_shortcut
      "parse_only" (KLong "parse-only") " stop after parsing";
    Debug.Args.desc_shortcut
      "type_only" (KLong "type-only") " stop after type checking";
    Termcode.opt_extra_expl_prefix;
    KLong "check-ce", Hnd0 (fun () -> opt_check_ce_model := true),
    " check counterexamples using runtime assertion checking\n\
     (RAC)";
    KLong "rac-prover", Hnd1 (AString, fun s -> opt_rac_prover := Some s),
    "<prover> use <prover> to check assertions in RAC when term\n\
     reduction is insufficient, with optional, comma-\n\
     separated time and memory limit (e.g. 'cvc4,2,1000')";
    KLong "rac-try-negate", Hnd0 (fun () -> opt_rac_try_negate := true),
    " try checking the negated term using the RAC prover when\n\
     the prover is defined and didn't give a result";
    Key ('v',"verbosity"), Hnd1(AInt, fun i -> opt_ce_check_verbosity := Some i),
    "<lvl> verbosity level for interpretation log of counterexam-\n\
     ple solver model";
    KLong "json", Hnd0 (fun () -> opt_json := Some `All),
    " print output in JSON format";
    KLong "json-model-values", Hnd0 (fun () -> opt_json := Some `Values),
    " print values of prover model in JSON format (back-\n\
     wards compatiblity with --json)";
  ]

let config, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

let opt_driver = ref (match !opt_driver with
  | f::ef -> Some (f, ef)
  | [] -> None)

let () = try
  if Queue.is_empty opt_queue then
    Whyconf.Args.exit_with_usage option_list usage_msg;

  if !opt_prover <> None && !opt_driver <> None then begin
    eprintf "Options '-P'/'--prover' and \
      '-D'/'--driver' cannot be used together.@.";
    exit 1
  end;

  if !opt_output <> None && !opt_driver = None && !opt_prover = None then begin
    eprintf
      "Option '-o'/'--output' requires either a prover or a driver.@.";
    exit 1
  end;

  if !opt_prover = None then begin
    if !opt_timelimit <> None then begin
      eprintf "Option '-t'/'--timelimit' requires a prover.@.";
      exit 1
    end;
    if !opt_stepslimit <> None then begin
      eprintf "Option '-t'/'--stepslimit' requires a prover.@.";
      exit 1
    end;
    if !opt_memlimit <> None then begin
      eprintf "Option '-m'/'--memlimit' requires a prover.@.";
      exit 1
    end;
    if !opt_driver = None && not !opt_print_namespace then
      opt_print_theory := true
  end;

  let main = Whyconf.get_main config in

  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);
  begin match !opt_prover with
  | Some s ->
    let filter_prover = Whyconf.parse_filter_prover s in
    let prover = Whyconf.filter_one_prover config filter_prover in
    let with_steps = !opt_stepslimit <> None in
    opt_command := Some (Whyconf.get_complete_command prover ~with_steps);
    opt_driver := Some (prover.driver, prover.extra_drivers)
  | None ->
      ()
  end;
  let add_meta task (meta,s) =
    let meta = lookup_meta meta in
    let args = match s with
      | Some s -> [MAstr s]
      | None -> []
    in
    Task.add_meta task meta args
  in
  opt_task := List.fold_left add_meta !opt_task !opt_metas

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let timelimit = match !opt_timelimit with
  | None -> 10
  | Some i when i <= 0 -> 0
  | Some i -> i

let stepslimit = Opt.get_def 0 !opt_stepslimit

let memlimit = match !opt_memlimit with
  | None -> 0
  | Some i when i <= 0 -> 0
  | Some i -> i

let print_th_namespace fmt th =
  Pretty.print_namespace fmt th.th_name.Ident.id_string th

let fname_printer = ref (Ident.create_ident_printer [])

let output_task drv fname _tname th task dir =
  let fname = Filename.basename fname in
  let fname =
    try Filename.chop_extension fname with _ -> fname in
  let tname = th.th_name.Ident.id_string in
  let dest = Driver.file_of_task drv fname tname task in
  (* Uniquify the filename before the extension if it exists*)
  let i = try String.rindex dest '.' with _ -> String.length dest in
  let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
  let ext = String.sub dest i (String.length dest - i) in
  let cout = open_out (Filename.concat dir (name ^ ext)) in
  Driver.print_task drv (formatter_of_out_channel cout) task;
  close_out cout

let print_result ?json fmt (fname, loc, goal_name, expls, res, ce) =
  match json with
  | Some `All ->
    let open Json_base in
    let print_loc fmt (loc, fname) =
      match loc with
      | None -> fprintf fmt "{%a}" (print_json_field "filename" print_json) (String fname)
      | Some loc -> Pretty.print_json_loc fmt loc in
    let print_term fmt (loc, fname, goal_name, expls) =
      fprintf fmt "@[@[<hv1>{%a;@ %a;@ %a@]}@]"
        (print_json_field "loc" print_loc) (loc, fname)
        (print_json_field "goal_name" print_json) (String goal_name)
        (print_json_field "explanations" print_json) (List (List.map (fun s -> String s) expls)) in
    fprintf fmt "@[@[<hv1>{%a;@ %a@]}@]"
      (print_json_field "term" print_term) (loc, fname, goal_name, expls)
      (print_json_field "prover-result" (Call_provers.print_prover_result ~json:true)) res
  | None | Some `Values as json ->
    ( match loc with
      | None -> fprintf fmt "File %s:@\n" fname
      | Some loc -> Loc.report_position fmt loc );
    ( if expls = [] then
        fprintf fmt "@[<hov>Verification@ condition@ @{<bold>%s@}.@]" goal_name
      else
        let expls = String.capitalize_ascii (String.concat ", " expls) in
        fprintf fmt
          "@[<hov>Goal@ @{<bold>%s@}@ from@ verification@ condition@ @{<bold>%s@}.@]"
          expls goal_name );
    fprintf fmt "@\n@[<hov2>Prover result is: %a.@]"
      (Call_provers.print_prover_result ~json:false) res;
    (match ce with
     | Some ce ->
        Counterexample.print_counterexample ?verb_lvl:!opt_ce_check_verbosity
          ~check_ce:!opt_check_ce_model ?json fmt ce
     | None -> ());
    fprintf fmt "@\n"

let unproved = ref false

let do_task env drv fname tname (th : Theory.theory) (task : Task.task) =
  let open Call_provers in
  let limit =
    { limit_time = timelimit;
      limit_mem = memlimit;
      limit_steps = stepslimit } in
  match !opt_output, !opt_command with
    | None, Some command ->
        let call = Driver.prove_task ~command ~limit drv task in
        let res = wait_on_call call in
        let ce =
          if res.pr_models <> [] then
            match Pmodule.restore_module th with
            | pm ->
               let reduce_config =
                 Pinterp.rac_reduce_config_lit config env
                   ~trans:"compute_in_goal" ?prover:!opt_rac_prover
                   ~try_negate:!opt_rac_try_negate () in
               Counterexample.select_model ~reduce_config
                 ~check:!opt_check_ce_model ?verb_lvl:!opt_ce_check_verbosity
                 env pm res.pr_models
            | exception Not_found -> None
          else None in
        let t = task_goal_fmla task in
        let expls = Termcode.get_expls_fmla t in
        let goal_name = (task_goal task).Decl.pr_name.Ident.id_string in
        printf "%a@." (print_result ?json:!opt_json)
          (fname, t.Term.t_loc, goal_name, expls, res, ce);
        let print_model fmt m =
          let print_attrs = Debug.(test_flag (lookup_flag "print_model_attrs"))  in
          if !opt_json = None then Model_parser.print_model_human fmt m ~print_attrs
          else Model_parser.print_model (* json values *) fmt m ~print_attrs in
        let print_other_models (m, ce_summary) =
          match ce_summary with
            | Counterexample.(NCCE log | SWCE log | NCCE_SWCE log) ->
                if !opt_print_original_model then
                  printf "@[<v>Original model:@\n%a@]@\n@." print_model m;
                if !opt_print_derived_model then
                  printf "@[<v>Derived model:@\n%a@]@\n@." print_model
                    (Counterexample.model_of_exec_log ~original_model:m log)
            | _ -> () in
        Opt.iter print_other_models ce;
        if res.pr_answer <> Valid then unproved := true
    | None, None ->
        Driver.print_task drv std_formatter task
    | Some dir, _ -> output_task drv fname tname th task dir

let do_tasks env drv fname tname th task =
  let lookup acc t =
    (try Trans.singleton (Trans.lookup_transform t env) with
       Trans.UnknownTrans _ -> Trans.lookup_transform_l t env) :: acc
  in
  let trans = List.fold_left lookup [] !opt_trans in
  let apply tasks tr =
    List.rev (List.fold_left (fun acc task ->
      List.rev_append (Trans.apply tr task) acc) [] tasks)
  in
  let tasks = List.fold_left apply [task] trans in
  List.iter (do_task env drv fname tname th) tasks

let do_theory env drv fname tname th glist elist =
  if !opt_print_theory then
    printf "%a@." Pretty.print_theory th
  else if !opt_print_namespace then
    printf "%a@." print_th_namespace th
  else begin
    let add acc (x,l) =
      let pr = try ns_find_pr th.th_export l with Not_found ->
        eprintf "Goal '%s' not found in theory '%s'.@." x tname;
        exit 1
      in
      Decl.Spr.add pr acc
    in
    let drv = Opt.get drv in
    let prs = Queue.fold add Decl.Spr.empty glist in
    let sel = if Decl.Spr.is_empty prs then None else Some prs in
    let tasks = Task.split_theory th sel !opt_task in
    List.iter (do_tasks env drv fname tname th) tasks;
    let eval (x,l) =
      let ls = try ns_find_ls th.th_export l with Not_found ->
        eprintf "Declaration '%s' not found in theory '%s'.@." x tname;
        exit 1
      in
      match Decl.find_logic_definition th.th_known ls with
      | None -> eprintf "Symbol '%s' has no definition in theory '%s'.@." x tname;
        exit 1
      | Some d ->
        let l,_t = Decl.open_ls_defn d in
        match l with
        | [] ->
(* TODO
          let t = Mlw_interp.eval_global_term env th.th_known t in
          printf "@[<hov 2>Evaluation of %s:@ %a@]@." x Mlw_interp.print_value t
*) ()
        | _ ->
          eprintf "Symbol '%s' is not a constant in theory '%s'.@." x tname;
          exit 1
    in
    Queue.iter eval elist
  end

let do_global_theory env drv (tname,p,t,glist,elist) =
  let th = Env.read_theory env p t in
  do_theory env drv "lib" tname th glist elist

let do_local_theory env drv fname m (tname,_,t,glist,elist) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory env drv fname tname th glist elist

let do_input env drv = function
  | None, _ when Debug.test_flag Typing.debug_type_only ||
                 Debug.test_flag Typing.debug_parse_only ->
      ()
  | None, tlist ->
      Queue.iter (do_global_theory env drv) tlist
  | Some f, tlist ->
      let format = !opt_parser in
      let fname, m = match f with
        | "-" -> "stdin",
            Env.read_channel Env.base_language ?format env "stdin" stdin
        | fname ->
            let (mlw_files, _) =
              Env.read_file Env.base_language ?format env fname in
            (fname, mlw_files)
      in
      if Debug.test_flag Typing.debug_type_only then ()
      else
        if Queue.is_empty tlist then
          let glist = Queue.create () in
          let elist = Queue.create () in
          let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
          let do_th _ (t,th) =
            do_theory env drv fname t th glist elist
          in
          Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
        else
          Queue.iter (do_local_theory env drv fname m) tlist

let () =
  try
    if Util.terminal_has_color then (
      Format.set_formatter_tag_functions Util.ansi_color_tags;
      set_mark_tags true );
    let load (f,ef) = load_driver_raw (Whyconf.get_main config) env f ef in
    let drv = Opt.map load !opt_driver in
    Queue.iter (do_input env drv) opt_queue;
    if !unproved then exit 2
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
