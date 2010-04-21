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

let usage_msg =
  "Usage: why [options] [[file|-] [-t <theory> [-g <goal>]...]...]..."

let opt_queue = Queue.create ()

let opt_input = ref None
let opt_theory = ref None

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

let add_opt_theory x =
  let l = Str.split (Str.regexp "\\.") x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match !opt_input, p with
  | None, [] ->
      eprintf "Option '-t'/'--theory' with a non-qualified \
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
      eprintf "Option '-g'/'--goal' requires a theory.@.";
      exit 1
  | Some glist ->
      let l = Str.split (Str.regexp "\\.") x in
      Queue.push (x, l) glist

let opt_config = ref None
let opt_prover = ref None
let opt_loadpath = ref []
let opt_driver = ref None
let opt_output = ref None
let opt_timelimit = ref None
let opt_memlimit = ref None
let opt_command = ref None

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false

let opt_parse_only = ref false
let opt_type_only = ref false
let opt_debug = ref false

let option_list = Arg.align [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-t", Arg.String add_opt_theory,
      "<theory> Select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -t";
  "-g", Arg.String add_opt_goal,
      "<goal> Select <goal> in the last selected theory";
  "--goal", Arg.String add_opt_goal,
      " same as -g";
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
  "-T", Arg.Int (fun i -> opt_timelimit := Some i),
      "<sec> Set the prover's time limit (default=10, no limit=0)";
  "--timelimit", Arg.Int (fun i -> opt_timelimit := Some i),
      " same as -T";
  "-M", Arg.Int (fun i -> opt_memlimit := Some i),
      "<MiB> Set the prover's memory limit (default: no limit)";
  "--memlimit", Arg.Int (fun i -> opt_timelimit := Some i),
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
      " Print the selected theories";
  "--print-namespace", Arg.Set opt_print_namespace,
      " Print the namespaces of selected theories";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List the registered transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List the registered printers";
  "--list-provers", Arg.Set opt_list_provers,
      " List the known provers";
  "--parse-only", Arg.Set opt_parse_only,
      " Stop after parsing";
  "--type-only", Arg.Set opt_type_only,
      " Stop after type checking";
  "--debug", Arg.Set opt_debug,
      " Set the debug flag"; ]

let () =
  Arg.parse option_list add_opt_file usage_msg;

  if !opt_list_transforms then
    printf "@[<hov 2>Registered transformations:@\n%a@]@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Driver.list_transforms ()));
  if !opt_list_printers then
    printf "@[<hov 2>Registered printers:@\n%a@]@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Driver.list_printers ()));
  if !opt_list_provers then begin
    let config = read_config !opt_config in
    let print fmt s prover = fprintf fmt "%s (%s)@\n" s prover.name in
    let print fmt m = Mstr.iter (print fmt) m in
    printf "@[<hov 2>Known provers:@\n%a@]@." print config.provers
  end;

  if !opt_list_transforms || !opt_list_printers || !opt_list_provers
  then exit 0;

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
      eprintf "Option '-T'/'--timelimit' requires a prover.@.";
      exit 1
    end;
    if !opt_memlimit <> None then begin
      eprintf "Option '-M'/'--memlimit' requires a prover.@.";
      exit 1
    end;
    if !opt_driver = None && not !opt_print_namespace then
      opt_print_theory := true
  end;

  let config = try read_config !opt_config with Not_found ->
    option_iter (eprintf "Config file '%s' not found.@.") !opt_config;
    option_iter
      (eprintf "No config file found (required by '-P %s').@.") !opt_prover;
    if !opt_config <> None || !opt_prover <> None then exit 1;
    { conf_file = "";
      loadpath  = [];
      timelimit = None;
      memlimit  = None;
      provers   = Mstr.empty }
  in

  opt_loadpath := List.rev_append !opt_loadpath config.loadpath;
  if !opt_timelimit = None then opt_timelimit := config.timelimit;
  if !opt_memlimit  = None then opt_memlimit  := config.memlimit;
  match !opt_prover with
  | Some s ->
      let prover = try Mstr.find s config.provers with
        | Not_found -> eprintf "Prover %s not found.@." s; exit 1
      in
      opt_command := Some prover.command;
      opt_driver := Some prover.driver
  | None ->
      ()

let timelimit = match !opt_timelimit with
  | None -> 10
  | Some i when i <= 0 -> 0
  | Some i -> i

let memlimit = match !opt_memlimit with
  | None -> 0
  | Some i when i <= 0 -> 0
  | Some i -> i

let debug = !opt_debug

let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Denv.Error e ->
      Denv.report fmt e
  | Typing.Error e ->
      Typing.report fmt e
  | Decl.UnknownIdent i ->
      fprintf fmt "anomaly: unknown ident '%s'" i.Ident.id_short
  | Driver.Error e ->
      Driver.report fmt e
  | Config.Dynlink.Error e ->
      fprintf fmt "Dynlink: %s" (Config.Dynlink.error_message e)
  | Whyconf.Error e ->
      fprintf fmt "Why config: %a" Whyconf.report e
  | e -> fprintf fmt "anomaly: %s" (Printexc.to_string e)

let print_th_namespace fmt th =
  Pretty.print_namespace fmt th.th_name.Ident.id_short th.th_export

let fname_printer = ref (Ident.create_ident_printer [])

let do_task _env drv fname tname (th : Why.Theory.theory) (task : Task.task) =
  match !opt_output, !opt_command with
    | None, Some command ->
        let res =
          Driver.prove_task ~debug ~command ~timelimit ~memlimit drv task ()
        in
        printf "%s %s %s : %a@." fname tname
          (task_goal task).Decl.pr_name.Ident.id_long
          Call_provers.print_prover_result res
    | None, None ->
        Driver.print_task drv std_formatter task
    | Some dir, _ ->
        let fname = Filename.basename fname in
        let fname =
          try Filename.chop_extension fname with _ -> fname
        in
        let tname = th.th_name.Ident.id_short in
        let dest = Driver.file_of_task drv fname tname task in
        (* Uniquify the filename before the extension if it exists*)
        let i = try String.rindex dest '.' with _ -> String.length dest in
        let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
        let ext = String.sub dest i (String.length dest - i) in
        let cout = open_out (Filename.concat dir (name ^ ext)) in
        Driver.print_task drv (formatter_of_out_channel cout) task;
        close_out cout

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
    let prs = Some (Queue.fold add Decl.Spr.empty glist) in
    let prs = if Queue.is_empty glist then None else prs in
    let tasks = split_theory th prs in
    let drv = Util.of_option drv in
    List.iter (do_task env drv fname tname th) tasks
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
      if !opt_parse_only then begin
        let lb = Lexing.from_channel cin in
        Loc.set_file fname lb;
        ignore (Lexer.parse_logic_file lb);
        close_in cin;
      end else begin
        let m = Typing.read_channel env fname cin in
        close_in cin;
        if !opt_type_only then ()
        else if Queue.is_empty tlist then
          let glist = Queue.create () in
          let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
          let do_th _ (t,th) = do_theory env drv fname t th glist in
          Ident.Mid.iter do_th (Mnm.fold add_th m Ident.Mid.empty)
        else
          Queue.iter (do_local_theory env drv fname m) tlist
      end

let () =
  try
    let env = Env.create_env (Typing.retrieve !opt_loadpath) in
    let drv = Util.option_map (load_driver env) !opt_driver in
    Queue.iter (do_input env drv) opt_queue
  with e when not debug ->
    eprintf "%a@." report e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
