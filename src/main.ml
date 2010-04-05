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

let opt_loadpath = ref []
let opt_driver = ref None
let opt_output = ref None
let opt_prove = ref false
let opt_timeout = ref None

let opt_print_theory = ref false
let opt_print_namespace = ref false
let opt_list_transforms = ref false
let opt_list_printers = ref false

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
  "-I", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--includes", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -I";
  "-D", Arg.String (fun s -> opt_driver := Some s),
      "<file> Specify the prover's driver file";
  "--driver", Arg.String (fun s -> opt_driver := Some s),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "-p", Arg.Set opt_prove,
      " Prove the selected goals";
  "--prove", Arg.Set opt_prove,
      " same as -p";
  "-T", Arg.Int (fun i -> opt_timeout := Some i),
      "<sec> Set the prover's time limit (default=10, no limit=0)";
  "--timeout", Arg.Int (fun i -> opt_timeout := Some i),
      " same as -T";
  "--print-theory", Arg.Set opt_print_theory,
      " Print the selected theories";
  "--print-namespace", Arg.Set opt_print_namespace,
      " Print the namespaces of selected theories";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List the registered transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List the registered printers";
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
  if !opt_list_transforms || !opt_list_printers then exit 0;

  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;

  if !opt_driver = None && not !opt_print_namespace then
    opt_print_theory := true;

  if !opt_driver = None && !opt_output <> None then begin
    eprintf "Option '-o'/'--output' requires a driver.@.";
    exit 1
  end;
  if !opt_driver = None && !opt_prove then begin
    eprintf "Option '-p'/'--prove' requires a driver.@.";
    exit 1
  end;
  if not !opt_prove && !opt_timeout <> None then begin
    eprintf "Option '-T'/'--timeout' requires '-p'/'--prove'.@.";
    exit 1
  end;
  if !opt_output <> None && !opt_prove then begin
    eprintf "Options '-o'/'--output' and \
      '-p'/'--prove' cannot be used together.@.";
    exit 1
  end

let timeout = match !opt_timeout with
  | None -> Some 10
  | Some i when i <= 0 -> None
  | Some i -> Some i

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
  | Dynlink_compat.Dynlink.Error e ->
      fprintf fmt "Dynlink : %s" (Dynlink_compat.Dynlink.error_message e)
  | e -> fprintf fmt "anomaly: %s" (Printexc.to_string e)

let print_th_namespace fmt th =
  Pretty.print_namespace fmt th.th_name.Ident.id_short th.th_export

let fname_printer = ref (Ident.create_ident_printer [])

let do_task env drv fname tname th task =
  if !opt_prove then begin
    let res = Driver.call_prover ~debug:!opt_debug ?timeout drv task in
    printf "%s %s %s : %a@." fname tname
      ((task_goal task).Decl.pr_name).Ident.id_long
      Call_provers.print_prover_result res
  end else match !opt_output with
    | None ->
        printf "@[%a@]@?" (Driver.print_task drv) task
    | Some dir ->
        try Unix.mkdir dir 0o755
        with Unix.Unix_error (Unix.EEXIST,_,_) -> ();
        let file =
          let file = Filename.basename fname in
          try Filename.chop_extension file
          with Invalid_argument _ -> file
        in
        let tname = th.th_name.Ident.id_short in
        let dest = Driver.filename_of_goal drv file tname task in
        (* Uniquify the filename before the extension if it exists*)
        let i = try String.rindex dest '.' with _ -> String.length dest in
        let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
        let ext = String.sub dest i (String.length dest - i) in
        let cout = open_out (Filename.concat dir (name ^ ext)) in
        let fmt = formatter_of_out_channel cout in
        fprintf fmt "@[%a@]@?" (Driver.print_task drv) task;
        close_out cout

let do_task env drv fname tname th task =
  let tasks = Driver.apply_transforms drv task in
  List.iter (do_task env drv fname tname th) tasks

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
          Mnm.iter (fun t th -> do_theory env drv fname t th glist) m
        else
          Queue.iter (do_local_theory env drv fname m) tlist
      end

let () =
  try
    let env = Env.create_env (Typing.retrieve !opt_loadpath) in
    let drv = Util.option_map (fun f -> load_driver f env) !opt_driver in
    Queue.iter (do_input env drv) opt_queue
  with e when not !opt_debug ->
    eprintf "%a@." report e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C .. byte"
End:
*)
