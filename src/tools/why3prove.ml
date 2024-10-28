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
open Why3
open Wstdlib
open Whyconf
open Theory
open Task

module Main : functor () -> sig end
 = functor () -> struct

let usage_msg =
  "[[<file>|-] [-T <theory> [-G <goal>]...]...]...\n\
   Run some transformation or prover on the given goals."

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []
(* Option for printing counterexamples with JSON formatting *)
let opt_json = ref false
let opt_check_ce_model = ref false
let opt_rac_prover = ref None
let opt_rac_timelimit = ref None
let opt_rac_memlimit = ref None
let opt_rac_steplimit = ref None
let opt_ce_log_verbosity = ref None
let opt_sub_goals = ref []

let debug_print_original_model = Debug.register_info_flag "print-original-model"
    ~desc:"Print original counterexample model when --check-ce"

let debug_print_derived_model = Debug.register_info_flag "print-derived-model"
    ~desc:"Print derived counterexample model when --check-ce"

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
      let msg = "Option '-T'/'--theory' with a non-qualified \
                 argument requires an input file." in
      raise (Getopt.GetoptFailure msg)
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
    | None, None ->
        let msg = "Option '-G'/'--goal' requires an input file or a library \
                   theory." in
        raise (Getopt.GetoptFailure msg)
    | None, Some _ ->
        add_opt_theory "Top";
        Option.get !opt_theory
    | Some glist, _ -> glist in
  let l = Strings.split '.' x in
  Queue.push (x, l) glist

let add_opt_trans x =
  match String.split_on_char ' ' x with
  | [] -> assert false
  | name :: args ->
      opt_trans := (name, args) :: !opt_trans

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

let subgoal_re = Re.Str.regexp "^\\([^:@]+\\)?\\(:[^@]+\\)?\\(@.+\\)?$"

let add_sub_goal s =
  let failure str =
    let msg = str ^ " for option --sub-goal" in
    raise (Getopt.GetoptFailure msg) in
  if Re.Str.string_match subgoal_re s 0 then (
    let f =
      try Re.Str.matched_group 1 s
      with Not_found ->
      try Option.get (fst (Queue.peek opt_queue))
      with _ -> failure "Missing file" in
    let l =
      try
        let s = Strings.remove_prefix ":" (Re.Str.matched_group 2 s) in
        Some (int_of_string s)
      with Not_found -> None | Failure _ -> failure "Invalid line number" in
    let e =
      try Some (Strings.remove_prefix "@" (Re.Str.matched_group 3 s))
      with Not_found -> None in
    opt_sub_goals := (f,l,e) :: !opt_sub_goals )
  else
    failure "Invalid argument"

let opt_driver : string list ref = ref []
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
let opt_color = ref false

let option_list =
  let open Getopt in
  [ Key ('T', "theory"), Hnd1 (AString, add_opt_theory),
    "<theory> select <theory> in the input file or in the library";
    Key ('G', "goal"), Hnd1 (AString, add_opt_goal),
    "<goal> select <goal> in the last selected theory";
    Key ('a', "apply-transform"), Hnd1 (AString, add_opt_trans),
    "<transf> apply a transformation to every task";
    Key ('g', "sub-goal"), Hnd1 (AString, add_sub_goal),
    "[<file>][:<line>][@<expl>] select sub-goals at the given\n\
     position and with the given explanation after applying\n\
     the transformations (<file> defaults to the input file)";
    Key ('P', "prover"), Hnd1 (AString, fun s -> opt_prover := Some s),
    "<prover> prove or print (with -o) the selected goals";
    Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    Key ('t', "timelimit"), Hnd1 (AFloat, fun i -> opt_timelimit := Some i),
    "<sec> set the prover's time limit (default=10, no limit=0)";
    Key ('s', "stepslimit"), Hnd1 (AInt, fun i -> opt_stepslimit := Some i),
    "<steps> set the prover's step limit (default: no limit)";
    Key ('m', "memlimit"), Hnd1 (AInt, fun i -> opt_memlimit := Some i),
    "<MiB> set the prover's memory limit (default: no limit)";
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
     reduction is insufficient, with optional, space-\n\
     separated time and memory limit (e.g. 'cvc4 2 1000')";
    KLong "rac-timelimit", Hnd1 (AFloat, fun i -> opt_rac_timelimit := Some i),
    "<sec> set the time limit for RAC (with --check-ce)";
    KLong "rac-memlimit", Hnd1 (AInt, fun i -> opt_rac_memlimit := Some i),
    "<steps> set the memory limit for RAC (with --check-ce)";
    KLong "rac-steplimit", Hnd1 (AInt, fun i -> opt_rac_steplimit := Some i),
    "<steps> set the step limit for RAC (with --check-ce)";
    KLong "ce-log-verbosity", Hnd1(AInt, fun i -> opt_ce_log_verbosity := Some i),
    "<lvl> verbosity level for interpretation log of\n\
    counterexample solver model";
    KLong "json", Hnd0 (fun () -> opt_json := true),
    " print output in JSON format";
    KLong "color", Hnd0 (fun () -> opt_color := true),
    " print output with colors";
  ]

let config, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

let opt_driver = ref (match !opt_driver with
  | f::ef -> Some (None,f,["",ef])
  | [] -> None)

let () = try
  if Queue.is_empty opt_queue then
    Whyconf.Args.exit_with_usage usage_msg;

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
    let (d,f) = prover.driver in
    opt_driver := Some(d,f,prover.extra_drivers)
  | None ->
      ()
  end;
  let add_meta task (meta,s) =
    let meta = lookup_meta meta in
    let args = match meta.meta_type, s with
      | [MTstring], Some s -> [MAstr s]
      | [MTint], Some s -> [MAint (int_of_string s)]
      | [], None -> []
      | _ -> failwith "meta argument not implemented"
    in
    Task.add_meta task meta args
  in
  opt_task := List.fold_left add_meta !opt_task !opt_metas

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let timelimit = match !opt_timelimit with
  | None -> 10.
  | Some i when i <= 0. -> 0.
  | Some i -> i

let stepslimit = Option.value ~default:0 !opt_stepslimit

let memlimit = match !opt_memlimit with
  | None -> 0
  | Some i when i <= 0 -> 0
  | Some i -> i

let print_th_namespace fmt th =
  Pretty.print_namespace th.th_name.Ident.id_string fmt th

let really_do_task (task: task) =
  let t = task_goal_fmla task in
  let aux (f,l,e) =
    match t.Term.t_loc with
    | None -> false
    | Some loc ->
        let goal_f, goal_l, _, _, _ = Loc.get loc in
        goal_f = f &&
        (match l with None -> true | Some l -> l = goal_l) &&
        (match e with None -> true | Some e ->
         let expls = String.concat " " (Termcode.get_expls_fmla t) in
         String.(equal (lowercase_ascii e) (lowercase_ascii expls))) in
  !opt_sub_goals = [] || List.exists aux !opt_sub_goals

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

(** Warning: when the json option is used, the counterexample model is taken from
    res (i.e., it is the prover supplied model, printed through Call Prover). Otherwise,
    the model is taken from ce (i.e., it is the model that went through the RAC pipeline)*)
let print_result json fmt (fname, loc, goal_name, expls, res, ce) =
  if json then
    begin
      let open Json_base in
      let loc =
        match loc with
        | None -> Record ["file-name", String fname]
        | Some loc ->
            let f, bl, bc, el, ec = Loc.get loc in
            Record [
                "file-name", String f;
                "start-line", Int bl;
                "start-char", Int bc;
                "end-line", Int el;
                "end-char", Int ec
              ] in
      let term =
        Record [
            "loc", loc;
            "goal_name", String goal_name;
            "explanations", List (List.map (fun s -> String s) expls)
          ] in
      print_json fmt
        (Record [
             "term", term;
             "prover-result", Call_provers.json_prover_result res
           ])
    end
  else
    begin
      ( match loc with
        | None -> fprintf fmt "File %s:@\n" fname
        | Some loc -> fprintf fmt "File %a:@\n" Loc.pp_position loc );
      ( if expls = [] then
          fprintf fmt "@[<hov>Goal@ @{<bold>%s@}.@]" goal_name
        else
          let expls = String.capitalize_ascii (String.concat ", " expls) in
          fprintf fmt
            "@[<hov>Sub-goal@ @{<bold>%s@}@ of@ goal@ @{<bold>%s@}.@]"
            expls goal_name );
      fprintf fmt "@\n@[<hov2>Prover result is: %a.@]"
        (Call_provers.print_prover_result ~json:false) res;
      Option.iter
        (Check_ce.print_model_classification ~json
           ?verb_lvl:!opt_ce_log_verbosity ~check_ce:!opt_check_ce_model env fmt)
        ce;
      fprintf fmt "@\n"
    end

let unproved = ref false

let select_ce env th models =
  if models <> [] then
    match Pmodule.restore_module th with
    | pm ->
        let main = Whyconf.get_main config in
        let limit_time = Whyconf.timelimit main in
        let limit_time = Opt.fold (fun _ s -> s) limit_time !opt_rac_timelimit in
        let limit_mem = Whyconf.memlimit main in
        let limit_mem = Opt.fold (fun _ s -> s) limit_mem !opt_rac_memlimit in
        let limit_steps = Opt.fold (fun _ s -> s) 0 !opt_rac_steplimit in
        let limits = Call_provers.{ limit_time ; limit_mem ; limit_steps } in
        let why_prover =
          match !opt_rac_prover with
          | None -> None
          | Some p -> Some(p,limits)
        in
        let rac = Pinterp.mk_rac ~ignore_incomplete:false
            (Rac.Why.mk_check_term_lit config env ~why_prover ()) in
        Check_ce.select_model ~limits ?verb_lvl:!opt_ce_log_verbosity
          ~check_ce:!opt_check_ce_model rac env pm models
    | exception Not_found -> None
  else None

let debug_print_model_attrs = Debug.lookup_flag "print_model_attrs"

(** TODO rewrite this old function *)
let print_other_models (m, (c, log)) =
  let print_model fmt m =
    let print_attrs = Debug.test_flag debug_print_model_attrs in
    Model_parser.print_model fmt m ~print_attrs
  in
  ( match c with
    | Check_ce.(NC | SW | NC_SW | BAD_CE _) ->
        if Debug.test_flag debug_print_original_model then
          printf "@[<v>Original model:@\n%a@]@\n@." print_model m;
    | _ -> () );
  ( match c with
    | Check_ce.(NC | SW | NC_SW) ->
        if Debug.test_flag debug_print_derived_model then
          printf "@[<v>Derived model:@\n%a@]@\n@." print_model
            (Check_ce.model_of_exec_log ~original_model:m log)
    | _ -> () )

let do_task config env drv fname tname (th : Theory.theory) (task : Task.task) =
  if really_do_task task then
  let open Call_provers in
  let limits =
    { limit_time = timelimit;
      limit_mem = memlimit;
      limit_steps = stepslimit } in
  match !opt_output, !opt_command with
    | None, Some command ->
        let call =
          Driver.prove_task ~command ~config ~limits drv task
        in
        let res = wait_on_call call in
        let ce = select_ce env th res.pr_models in
        let t = task_goal_fmla task in
        let expls = Termcode.get_expls_fmla t in
        let goal_name = (task_goal task).Decl.pr_name.Ident.id_string in
        printf "%a@." (print_result !opt_json)
          (fname, t.Term.t_loc, goal_name, expls, res, ce);
        Option.iter print_other_models ce;
        if res.pr_answer <> Valid then unproved := true
    | None, None ->
        Driver.print_task drv std_formatter task
    | Some dir, _ -> output_task drv fname tname th task dir

let do_tasks config env drv fname tname th task =
  let table = Args_wrapper.build_naming_tables task in
  let rec apply tasks = function
    | [] -> tasks
    | (name, args) :: trans ->
        let apply_trans =
          if args = [] then
            Trans.apply_transform name env
          else
            let ffmt = Env.get_format ?format:!opt_parser fname in
            Trans.apply_transform_args name env args table ffmt in
        apply (List.concat (List.map apply_trans tasks)) trans in
  let tasks = apply [task] !opt_trans in
  List.iter (do_task config env drv fname tname th) tasks

let do_theory config env drv fname tname th glist elist =
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
    let drv = Option.get drv in
    let prs = Queue.fold add Decl.Spr.empty glist in
    let sel = if Decl.Spr.is_empty prs then None else Some prs in
    let tasks = Task.split_theory th sel !opt_task in
    List.iter (do_tasks config env drv fname tname th) tasks;
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

let do_global_theory config env drv (tname,p,t,glist,elist) =
  let th = Env.read_theory env p t in
  do_theory config env drv "lib" tname th glist elist

let do_local_theory config env drv fname m (tname,_,t,glist,elist) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory config env drv fname tname th glist elist

let do_input config env drv = function
  | None, _ when Debug.test_flag Typing.debug_type_only ||
                 Debug.test_flag Typing.debug_parse_only ->
      ()
  | None, tlist ->
      Queue.iter (do_global_theory config env drv) tlist
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
            do_theory config env drv fname t th glist elist
          in
          Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
        else
          Queue.iter (do_local_theory config env drv fname m) tlist

let () =
  try
    if (Util.terminal_has_color && !opt_color) then (
      Format.set_formatter_stag_functions Util.ansi_color_tags;
      set_mark_tags true );
    let main = Whyconf.get_main config in
    let load (d,f,ef) = Driver.load_driver_file_and_extras main env ~extra_dir:d f ef in
    let drv = Option.map load !opt_driver in
    Queue.iter (do_input main env drv) opt_queue;
    if !unproved then exit 2
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

end

let () = Whyconf.register_command "prove" (module Main)
