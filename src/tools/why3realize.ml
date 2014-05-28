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

open Format
open Why3
open Stdlib
open Theory
open Driver

let usage_msg = sprintf
  "Usage: %s [options] [[file|-] [-T <theory> [-G <goal>]...]...]..."
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 platform, version %s (build date: %s)"
  Config.version Config.builddate

let opt_queue = Queue.create ()

let opt_input = ref None

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
      Queue.push (x, p, t) tlist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      Queue.push (x, p, t) tlist

let opt_parser = ref None
let opt_driver = ref None
let opt_output = ref None
let opt_task = ref None

let opt_print_libdir = ref false
let opt_print_datadir = ref false

let option_list = [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " Read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> Select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> Select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-D", Arg.String (fun s -> opt_driver := Some (s, [])),
      "<file> Specify a prover's driver (conflicts with -P)";
  "--driver", Arg.String (fun s -> opt_driver := Some (s, [])),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print the selected goals to separate files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o" ]

let (env, config) =
  Args.initialize option_list add_opt_file usage_msg

let () =
  if Queue.is_empty opt_queue then begin
    Arg.usage option_list usage_msg;
    exit 1
  end;
  if !opt_driver = None then begin
    eprintf "Driver (-D) is required.@.";
    exit 1
  end

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
  match !opt_output with
  | Some dir ->
    output_theory drv fname tname th task dir
  | None ->
    eprintf "Output directory (-o) is required.@.";
    exit 1

let do_theory drv fname tname th =
  if th.th_path = [] then begin
    eprintf "Theory %s is not from the library.@." tname;
    exit 1
  end;
  let drv = Opt.get drv in
  let task = Task.use_export !opt_task th in
  do_task drv fname tname th task

let do_global_theory env drv (tname,p,t) =
  let format = Opt.get_def "why" !opt_parser in
  let th = try Env.read_theory ~format env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." tname;
    exit 1
  in
  do_theory drv "lib" tname th

let do_local_theory drv fname m (tname,_,t) =
  let th = try Mstr.find t m with Not_found ->
    eprintf "Theory '%s' not found in file '%s'.@." tname fname;
    exit 1
  in
  do_theory drv fname tname th

let do_input env drv = function
  | None, tlist ->
      Queue.iter (do_global_theory env drv) tlist
  | Some f, tlist ->
    let fname, cin = match f with
      | "-" -> "stdin", stdin
      | f   -> f, open_in f
    in
    let m = Env.read_channel ?format:!opt_parser env fname cin in
    close_in cin;
    if Queue.is_empty tlist then
      let add_th t th mi = Ident.Mid.add th.th_name (t,th) mi in
      let do_th _ (t,th) = do_theory drv fname t th in
      Ident.Mid.iter do_th (Mstr.fold add_th m Ident.Mid.empty)
    else
      Queue.iter (do_local_theory drv fname m) tlist

let driver_file s =
  if Sys.file_exists s || String.contains s '/' || String.contains s '.' then
    s
  else
    Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv"))

let load_driver env (s,ef) =
  let file = driver_file s in
  load_driver env file ef

let () =
  try
    let drv = Opt.map (load_driver env) !opt_driver in
    Queue.iter (do_input env drv) opt_queue
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
