(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Util
open Whyconf
open Theory
open Task
open Driver

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]..."
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 platform, version %s (build date: %s)"
  Config.version Config.builddate

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory =
  let rdot = (Str.regexp "\\.") in fun x ->
  let l = Str.split rdot x in
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
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      let glist = Queue.create () in
      Queue.push (x, p, t, glist) tlist;
      opt_theory := Some glist

let add_opt_goal x = match !opt_theory with
  | None ->
      eprintf "Option '-G'/'--goal' requires a theory.@.";
      exit 1
  | Some glist ->
      let l = Str.split (Str.regexp "\\.") x in
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

let opt_config = ref None
let opt_extra = ref []
let opt_parser = ref None
let opt_prover = ref None
let opt_loadpath = ref []
let opt_driver = ref None
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_command = ref None
let opt_task = ref None
let opt_realize = ref false
let opt_extract = ref None
let opt_bisect = ref false

let opt_print_libdir = ref false
let opt_print_datadir = ref false

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false

let opt_token_count = ref false
let opt_parse_only = ref false
let opt_type_only = ref false
let opt_version = ref false

let option_list = Arg.align [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> Select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-G", Arg.String add_opt_goal,
      "<goal> Select <goal> in the last selected theory";
  "--goal", Arg.String add_opt_goal,
      " same as -G";
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> Read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  "-I", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L (obsolete)";
  "-P", Arg.String (fun s -> opt_prover := Some s),
      "<prover> Prove or print (with -o) the selected goals";
  "--prover", Arg.String (fun s -> opt_prover := Some s),
      " same as -P";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> Select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-t", Arg.Int (fun i -> opt_timelimit := Some i),
      "<sec> Set the prover's time limit (default=10, no limit=0)";
  "--timelimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -t";
  "-m", Arg.Int (fun i -> opt_memlimit := Some i),
      "<MiB> Set the prover's memory limit (default: no limit)";
  "--memlimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -m";
  "-a", Arg.String add_opt_trans,
      "<transformation> Apply a transformation to every task";
  "--apply-transform", Arg.String add_opt_trans,
      " same as -a";
  "-M", Arg.String add_opt_meta,
      "<meta_name>[=<string>] Add a meta to every task";
  "--meta", Arg.String add_opt_meta,
      " same as -M";
  "-D", Arg.String (fun s -> opt_driver := Some (s, [])),
      "<file> Specify a prover's driver (conflicts with -P)";
  "--driver", Arg.String (fun s -> opt_driver := Some (s, [])),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "--realize", Arg.Set opt_realize,
      " Realize selected theories from the library";
  "-E", Arg.String (fun s -> opt_extract := Some s),
      "<driver> Generate code for selected theories/modules";
  "--extract", Arg.String (fun s -> opt_extract := Some s),
      " same as -E";
  "--bisect", Arg.Set opt_bisect,
      " Reduce the set of needed axioms which prove a goal, \
        and output the resulting task";
  "--print-theory", Arg.Set opt_print_theory,
      " Print selected theories";
  "--print-namespace", Arg.Set opt_print_namespace,
      " Print namespaces of selected theories";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List known transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List known printers";
  "--list-provers", Arg.Set opt_list_provers,
      " List known provers";
  "--list-formats", Arg.Set opt_list_formats,
      " List known input formats";
  "--list-metas", Arg.Set opt_list_metas,
      " List known metas";
  Debug.Args.desc_debug_list;
  "--token-count", Arg.Set opt_token_count,
      " Only lexing, and give numbers of tokens in spec vs in program";
  Debug.Args.desc_shortcut "parse_only" "--parse-only" " Stop after parsing";
  Debug.Args.desc_shortcut
    "type_only" "--type-only" " Stop after type checking";
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug;
  "--print-libdir", Arg.Set opt_print_libdir,
      " Print location of binary components (plugins, etc)";
  "--print-datadir", Arg.Set opt_print_datadir,
      " Print location of non-binary data (theories, modules, etc)";
  "--version", Arg.Set opt_version,
      " Print version information" ]

let () = try
  Arg.parse option_list add_opt_file usage_msg;

  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end;
  if !opt_print_libdir then begin
    printf "%s@." Config.libdir;
    exit 0
  end;
  if !opt_print_datadir then begin
    printf "%s@." Config.datadir;
    exit 0
  end;

  (** Configuration *)
  let config = read_config !opt_config in
  let config = List.fold_left merge_config config !opt_extra in
  let main = get_main config in
  Whyconf.load_plugins main;

  Debug.Args.set_flags_selected ();

  (** listings*)

  let sort_pair (x,_) (y,_) = String.compare x y in
  let opt_list = ref false in
  if !opt_list_transforms then begin
    opt_list := true;
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 Trans.print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 Trans.print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms_l ()))
  end;
  if !opt_list_printers then begin
    opt_list := true;
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 Printer.print_printer_desc)
      (List.sort sort_pair (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l, f) =
      fprintf fmt "@[%s [%a]@\n  @[%a@]@]"
        p (Pp.print_list Pp.comma print1) l
        Pp.formatted f
    in
    printf "@[Known input formats:@\n  @[%a@]@]@."
      (Pp.print_list Pp.newline2 print)
      (List.sort Pervasives.compare (Env.list_formats ()))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let print = Pp.print_iter2 Mprover.iter Pp.newline Pp.nothing
      print_prover Pp.nothing in
    let provers = get_provers config in
    printf "@[<hov 2>Known provers:@\n%a@]@." print provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[<h 2>%s %s%a@\n@[<hov>%a@]@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "(flag) " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
      Pp.formatted m.meta_desc
    in
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print) (List.sort cmp (Theory.list_metas ()))
  end;
  opt_list :=  Debug.Args.option_list () || !opt_list;
  if !opt_list then exit 0;

  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;

  if !opt_prover <> None && !opt_driver <> None then begin
    eprintf "Options '-P'/'--prover' and \
      '-D'/'--driver' cannot be used together.@.";
    exit 1
  end;

  if !opt_output <> None
  && !opt_driver = None && !opt_prover = None && !opt_extract = None then begin
    eprintf
      "Option '-o'/'--output' requires a prover, a driver, or option '-E'.@.";
    exit 1
  end;

  if !opt_prover = None then begin
    if !opt_timelimit <> None then begin
      eprintf "Option '-t'/'--timelimit' requires a prover.@.";
      exit 1
    end;
    if !opt_memlimit <> None then begin
      eprintf "Option '-m'/'--memlimit' requires a prover.@.";
      exit 1
    end;
    if !opt_bisect then begin
      eprintf "Option '--bisect' requires a prover.@.";
      exit 1
    end;
    if !opt_driver = None && not !opt_print_namespace then
      opt_print_theory := true
  end;

  if !opt_extract <> None && !opt_output = None then begin
    eprintf
      "Option '-E'/'--extract' require a directory to output the result.@.";
    exit 1
  end;

  if !opt_bisect && !opt_output = None then begin
    eprintf "Option '--bisect' require a directory to output the result.@.";
    exit 1
  end;

  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  if !opt_timelimit = None then opt_timelimit := Some (Whyconf.timelimit main);
  if !opt_memlimit  = None then opt_memlimit  := Some (Whyconf.memlimit main);
  begin match !opt_prover with
  | Some s ->
    let filter_prover = Whyconf.parse_filter_prover s in
    let prover = Whyconf.filter_one_prover config filter_prover in
    opt_command :=
      Some (String.concat " " (prover.command :: prover.extra_options));
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
    add_meta task meta args
  in
  opt_task := List.fold_left add_meta !opt_task !opt_metas

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let timelimit = match !opt_timelimit with
  | None -> 10
  | Some i when i <= 0 -> 0
  | Some i -> i

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

let output_task_prepared drv fname _tname th task dir =
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
  Driver.print_task_prepared drv (formatter_of_out_channel cout) task;
  close_out cout

let output_theory drv fname _tname th task dir =
  let fname = Filename.basename fname in
  let fname =
    try Filename.chop_extension fname with _ -> fname in
  let dest = Driver.file_of_theory drv fname th in
  let file = Filename.concat dir dest in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  Driver.print_task ?old drv (formatter_of_out_channel cout) task;
  close_out cout

let do_task drv fname tname (th : Theory.theory) (task : Task.task) =
  match !opt_output, !opt_command with
    | Some dir, _ when !opt_realize ->
        output_theory drv fname tname th task dir
    | None, _ when !opt_realize ->
        eprintf "Output directory (-o) is required.@.";
        exit 1
    | Some dir, Some command when !opt_bisect ->
        let test task =
          let call = Driver.prove_task
            ~command ~timelimit ~memlimit drv task in
          let res = Call_provers.wait_on_call (call ()) () in
          printf "%s %s %s : %a@." fname tname
            (task_goal task).Decl.pr_name.Ident.id_string
            Call_provers.print_prover_result res;
          res.Call_provers.pr_answer = Call_provers.Valid in
        if not (test task)
        then printf "I can't bisect %s %s %s which is not valid@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_string
        else
          let rem = Eliminate_definition.bisect test task in
          let goal,task = Task.task_separate_goal task in
          let task = List.fold_left
            (fun task (m,ml) -> Task.add_meta task m ml) task rem in
          let task = add_tdecl task goal in
          (** We suppose here that the first transformation in the driver
              is remove_builtin *)
          let prepared_task = Driver.prepare_task drv task in
          output_task_prepared drv fname tname th prepared_task dir
    | None, Some command ->
        let call = Driver.prove_task ~command ~timelimit ~memlimit drv task in
        let res = Call_provers.wait_on_call (call ()) () in
        printf "%s %s %s : %a@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_string
          Call_provers.print_prover_result res
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
  List.iter (do_task drv fname tname th) tasks

let do_theory env drv fname tname th glist =
  if !opt_print_theory then
    printf "%a@." Pretty.print_theory th
  else if !opt_print_namespace then
    printf "%a@." print_th_namespace th
  else if !opt_realize then
    if th.th_path = [] then begin
      eprintf "Theory %s is not from the library.@." tname;
      exit 1
    end else if not (Queue.is_empty glist) then begin
      eprintf "Cannot realize individual goals.@.";
      exit 1
    end else begin
      let drv = Opt.get drv in
      let task = Task.use_export None th in
      do_tasks env drv fname tname th task
    end
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
    let tasks = List.rev (split_theory th sel !opt_task) in
    List.iter (do_tasks env drv fname tname th) tasks
  end

let do_global_theory env drv (tname,p,t,glist) =
  let format = Opt.get_def "why" !opt_parser in
  let th = try Env.read_theory ~format env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." tname;
    exit 1
  in
  do_theory env drv "lib" tname th glist

let do_local_theory env drv fname m (tname,_,t,glist) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory env drv fname tname th glist

(* program extraction *)

let extract_to ?fname th extract =
  let dir = Opt.get !opt_output in
  let file = Filename.concat dir (Mlw_ocaml.extract_filename ?fname th) in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  extract file ?old (formatter_of_out_channel cout);
  close_out cout

let do_extract_theory edrv ?fname tname th =
  let extract file ?old fmt = ignore (old);
    Debug.dprintf Mlw_ocaml.debug "extract theory %s to file %s@." tname file;
    Mlw_ocaml.extract_theory edrv ?old ?fname fmt th
  in
  extract_to ?fname th extract

let do_extract_module edrv ?fname tname m =
  let extract file ?old fmt = ignore (old);
    Debug.dprintf Mlw_ocaml.debug "extract module %s to file %s@." tname file;
    Mlw_ocaml.extract_module edrv ?old ?fname fmt m
  in
  extract_to ?fname m.Mlw_module.mod_theory extract

let do_global_extract edrv (tname,p,t,_) =
  let lib = edrv.Mlw_driver.drv_lib in
  try
    let mm, thm = Env.read_lib_file lib p in
    try
      let m = Mstr.find t mm in
      do_extract_module edrv tname m
    with Not_found ->
      let th = Mstr.find t thm in
      do_extract_theory edrv tname th
  with Env.LibFileNotFound _ | Not_found -> try
    let format = Opt.get_def "why" !opt_parser in
    let env = Env.env_of_library lib in
    let th = Env.read_theory ~format env p t in
    do_extract_theory edrv tname th
  with Env.LibFileNotFound _ | Env.TheoryNotFound _ ->
    eprintf "Theory/module '%s' not found.@." tname;
    exit 1

let do_extract_theory_from env fname m (tname,_,t,_) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_extract_theory env ~fname tname th

let do_extract_module_from env fname mm thm (tname,_,t,_) =
  try
    let m = Mstr.find t mm in do_extract_module env ~fname tname m
  with Not_found -> try
    let th = Mstr.find t thm in do_extract_theory env ~fname tname th
  with Not_found ->
    eprintf "Theory/module '%s' not found in file '%s'.@." tname fname;
    exit 1

let do_local_extract edrv fname cin tlist =
  let lib = edrv.Mlw_driver.drv_lib in
  if !opt_parser = Some "whyml" || Filename.check_suffix fname ".mlw" then begin
    let mm, thm = Mlw_main.read_channel lib [] fname cin in
    if Queue.is_empty tlist then begin
      let do_m t m thm =
        do_extract_module edrv ~fname t m; Mstr.remove t thm in
      let thm = Mstr.fold do_m mm thm in
      Mstr.iter (fun t th -> do_extract_theory edrv ~fname t th) thm
    end else
      Queue.iter (do_extract_module_from edrv fname mm thm) tlist
  end else begin
    let env = Env.env_of_library lib in
    let m = Env.read_channel ?format:!opt_parser env fname cin in
    if Queue.is_empty tlist then
      let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
      let do_th _ (t,th) = do_extract_theory edrv ~fname t th in
      Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
    else
      Queue.iter (do_extract_theory_from edrv fname m) tlist
  end

let total_annot_tokens = ref 0
let total_program_tokens = ref 0

let do_input env drv edrv = function
  | None, _ when !opt_parse_only || !opt_type_only ->
      ()
  | None, tlist when edrv <> None ->
      Queue.iter (do_global_extract (Opt.get edrv)) tlist
  | None, tlist ->
      Queue.iter (do_global_theory env drv) tlist
  | Some f, tlist ->
      let fname, cin = match f with
        | "-" -> "stdin", stdin
        | f   -> f, open_in f
      in
      if !opt_token_count then begin
        let lb = Lexing.from_channel cin in
        let a,p = Lexer.token_counter lb in
        close_in cin;
        if a = 0 then begin
          (* hack: we assume it is a why file and not a mlw *)
          total_annot_tokens := !total_annot_tokens + p;
          Format.printf "File %s: %d tokens@." f p;
        end else begin
          total_program_tokens := !total_program_tokens + p;
          total_annot_tokens := !total_annot_tokens + a;
          Format.printf "File %s: %d tokens in annotations@." f a;
          Format.printf "File %s: %d tokens in programs@." f p
        end
      end else if edrv <> None then begin
        do_local_extract (Opt.get edrv) fname cin tlist;
        close_in cin
      end else begin
        let m = Env.read_channel ?format:!opt_parser env fname cin in
        close_in cin;
        if !opt_type_only then
          ()
        else
          if Queue.is_empty tlist then
            let glist = Queue.create () in
            let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
            let do_th _ (t,th) = do_theory env drv fname t th glist in
            Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
          else
            Queue.iter (do_local_theory env drv fname m) tlist
      end

let driver_file s =
  if Sys.file_exists s || String.contains s '/' || String.contains s '.' then
    s
  else
    Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv"))

let load_driver env (s,ef) =
  let file = driver_file s in
  load_driver env file ef

let load_driver_extract env s =
  let file = driver_file s in
  let lib = Mlw_main.library_of_env env in
  Mlw_driver.load_driver lib file []

let () =
  try
    let env = Env.create_env !opt_loadpath in
    let drv = Opt.map (load_driver env) !opt_driver in
    let edrv = Opt.map (load_driver_extract env) !opt_extract in
    Queue.iter (do_input env drv edrv) opt_queue;
    if !opt_token_count then
      Format.printf "Total: %d annot/%d programs, ratio = %.3f@."
        !total_annot_tokens !total_program_tokens
        ((float !total_annot_tokens) /. (float !total_program_tokens))
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
