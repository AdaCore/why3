(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Why
open Util
open Whyconf
open Theory
open Task
open Driver
open Trans

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]..."
  (Filename.basename Sys.argv.(0))

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None
let opt_trans = ref []
let opt_metas = ref []
let opt_debug = ref []

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

let add_opt_debug x = opt_debug := x::!opt_debug

let add_opt_meta meta =
  let meta_name, meta_arg =
    let index = String.index meta '=' in
    (String.sub meta 0 index),
    (String.sub meta (index+1) (String.length meta - (index + 1))) in
  opt_metas := (meta_name,meta_arg)::!opt_metas

let opt_config = ref None
let opt_parser = ref None
let opt_prover = ref None
let opt_loadpath = ref []
let opt_driver = ref None
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_command = ref None
let opt_task = ref None

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_flags = ref false

let opt_parse_only = ref false
let opt_type_only = ref false
let opt_debug_all = ref false

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
      "<meta_name>=<string> Add a string meta to every task";
  "--meta", Arg.String add_opt_meta,
      " same as -M";
  "-D", Arg.String (fun s -> opt_driver := Some s),
      "<file> Specify a prover's driver (conflicts with -P)";
  "--driver", Arg.String (fun s -> opt_driver := Some s),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
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
  "--list-debug-flags", Arg.Set opt_list_flags,
      " List known debug flags";
  "--parse-only", Arg.Set opt_parse_only,
      " Stop after parsing (same as --debug parse_only)";
  "--type-only", Arg.Set opt_type_only,
      " Stop after type checking (same as --debug type_only)";
  "--debug-all", Arg.Set opt_debug_all,
      " Set every known debug flag";
  "--debug", Arg.String add_opt_debug,
      "<flag> Set a debug flag" ]

let () =
  Arg.parse option_list add_opt_file usage_msg;

  (* TODO? : Since drivers can dynlink ml code they can add printer,
     transformations, ... So drivers should be loaded before listing *)
  let opt_list = ref false in
  if !opt_list_transforms then begin
    opt_list := true;
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Trans.list_transforms_l ()));
  end;
  if !opt_list_printers then begin
    opt_list := true;
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l) =
      fprintf fmt "%s [%a]" p (Pp.print_list Pp.comma print1) l
    in
    printf "@[<hov 2>Known input formats:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Env.list_formats ()))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let config = read_config !opt_config in
    let print fmt s prover = fprintf fmt "%s (%s)@\n" s prover.name in
    let print fmt m = Mstr.iter (print fmt) m in
    printf "@[<hov 2>Known provers:@\n%a@]@." print config.provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[%s %s%a@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "* " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
    in
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline print) (List.sort cmp (Theory.list_metas ()))
  end;
  if !opt_list_flags then begin
    opt_list := true;
    let print fmt (p,_,_) = fprintf fmt "%s" p in
    printf "@[<hov 2>Known debug flags:@\n%a@]@."
      (Pp.print_list Pp.newline print)
      (List.sort Pervasives.compare (Debug.list_flags ()))
  end;
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

  if !opt_prover = None then begin
    if !opt_driver = None && !opt_output <> None then begin
      eprintf "Option '-o'/'--output' requires a prover or a driver.@.";
      exit 1
    end;
    if !opt_timelimit <> None then begin
      eprintf "Option '-t'/'--timelimit' requires a prover.@.";
      exit 1
    end;
    if !opt_memlimit <> None then begin
      eprintf "Option '-m'/'--memlimit' requires a prover.@.";
      exit 1
    end;
    if !opt_driver = None && not !opt_print_namespace then
      opt_print_theory := true
  end;

  if !opt_debug_all then
    List.iter (fun (_,f,_) -> Debug.set_flag f) (Debug.list_flags ());

  List.iter (fun s -> Debug.set_flag (Debug.lookup_flag s)) !opt_debug;

  if !opt_parse_only then Debug.set_flag Typing.debug_parse_only;
  if !opt_type_only then Debug.set_flag Typing.debug_type_only;

  let config = try read_config !opt_config with Not_found ->
    option_iter (eprintf "Config file '%s' not found.@.") !opt_config;
    option_iter
      (eprintf "No config file found (required by '-P %s').@.") !opt_prover;
    if !opt_config <> None || !opt_prover <> None then exit 1;
    default_config
  in

  opt_loadpath := List.rev_append !opt_loadpath config.main.loadpath;
  if !opt_timelimit = None then opt_timelimit := Some config.main.timelimit;
  if !opt_memlimit  = None then opt_memlimit  := Some config.main.memlimit;
  begin match !opt_prover with
  | Some s ->
      let prover = try Mstr.find s config.provers with
        | Not_found -> eprintf "Driver %s not found.@." s; exit 1
      in
      opt_command := Some prover.command;
      opt_driver := Some prover.driver
  | None ->
    () end;
  let add_meta task (meta,s) =
    let meta = lookup_meta meta in
    add_meta task meta [MAstr s] in
  opt_task := List.fold_left add_meta !opt_task !opt_metas

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

let do_task drv fname tname (th : Why.Theory.theory) (task : Task.task) =
  match !opt_output, !opt_command with
    | None, Some command ->
        let res =
          Driver.prove_task ~command ~timelimit ~memlimit drv task ()
        in
        printf "%s %s %s : %a@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_string
          Call_provers.print_prover_result res
    | None, None ->
        Driver.print_task drv std_formatter task
    | Some dir, _ ->
        let fname = Filename.basename fname in
        let fname =
          try Filename.chop_extension fname with _ -> fname
        in
        let tname = th.th_name.Ident.id_string in
        let dest = Driver.file_of_task drv fname tname task in
        (* Uniquify the filename before the extension if it exists*)
        let i = try String.rindex dest '.' with _ -> String.length dest in
        let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
        let ext = String.sub dest i (String.length dest - i) in
        let cout = open_out (Filename.concat dir (name ^ ext)) in
        Driver.print_task drv (formatter_of_out_channel cout) task;
        close_out cout

let do_tasks env drv fname tname th task =
  let lookup acc t =
    (try t, Trans.singleton (Trans.lookup_transform t env) with
       Trans.UnknownTrans _ -> t, Trans.lookup_transform_l t env) :: acc
  in
  let trans = List.fold_left lookup [] !opt_trans in
  let apply tasks (s, tr) =
    List.rev (List.fold_left (fun acc task ->
      List.rev_append (Trans.apply_named s tr task) acc) [] tasks)
  in
  let tasks = List.fold_left apply [task] trans in
  List.iter (do_task drv fname tname th) tasks

let do_theory env drv fname tname th glist =
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
    let drv = Util.of_option drv in
    let prs = Queue.fold add Decl.Spr.empty glist in
    let sel = if Decl.Spr.is_empty prs then None else Some prs in
    let tasks = List.rev (split_theory th sel !opt_task) in
    List.iter (do_tasks env drv fname tname th) tasks
  end

let do_global_theory env drv (tname,p,t,glist) =
  let th = try Env.find_theory env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." tname;
    exit 1
  in
  do_theory env drv "lib" tname th glist

let do_local_theory env drv fname m (tname,_,t,glist) =
  let th = try Mnm.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory env drv fname tname th glist

let do_input env drv = function
  | None, _ when !opt_parse_only || !opt_type_only ->
      ()
  | None, tlist ->
      Queue.iter (do_global_theory env drv) tlist
  | Some f, tlist ->
      let fname, cin = match f with
        | "-" -> "stdin", stdin
        | f   -> f, open_in f
      in
      let m = Env.read_channel ?name:!opt_parser env fname cin in
      close_in cin;
      if !opt_type_only then
        ()
      else if Queue.is_empty tlist then
        let glist = Queue.create () in
        let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
        let do_th _ (t,th) = do_theory env drv fname t th glist in
        Ident.Mid.iter do_th (Mnm.fold add_th m Ident.Mid.empty)
      else
        Queue.iter (do_local_theory env drv fname m) tlist

let () =
  try
    let env = Env.create_env (Lexer.retrieve !opt_loadpath) in
    let drv = Util.option_map (load_driver env) !opt_driver in
    Queue.iter (do_input env drv) opt_queue
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
