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

let usage_msg = sprintf
  "Usage: %s [options] -D <driver> -o <dir> -T <theory> ..."
  (Filename.basename Sys.argv.(0))

let opt_queue = Queue.create ()

let add_opt_file _ =
  eprintf "Realization only works for theories in the loadpath,@\n\
    not for files specified on the command line.@\n\
    Use option -L if the containing files are not in the default loadpath.@.";
  exit 1

let add_opt_theory x =
  let l = Strings.split '.' x in
  let p, t = match List.rev l with
    | t::p -> List.rev p, t
    | _ -> assert false
  in
  match p with
  | [] ->
      eprintf "Option '-T'/'--theory' requires a qualified argument.@.";
      exit 1
  | _ ->
      Queue.push (x, p, t) opt_queue

let opt_parser = ref None
let opt_driver = ref None
let opt_output = ref None

let option_list = [
  "-T", Arg.String add_opt_theory,
      "<theory> select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-D", Arg.String (fun s -> opt_driver := Some s),
      "<file> specify a realization driver";
  "--driver", Arg.String (fun s -> opt_driver := Some s),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> write the realizations in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o" ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

let () =
  if Queue.is_empty opt_queue then
    Whyconf.Args.exit_with_usage option_list usage_msg

let opt_output =
  match !opt_output with
  | None ->
    eprintf "Output directory (-o) is required.@.";
    exit 1
  | Some d -> d

let opt_driver =
  match !opt_driver with
  | None ->
    eprintf "Driver (-D) is required.@.";
    exit 1
  | Some s ->
    let s =
      if Sys.file_exists s || String.contains s '/' || String.contains s '.' then s
      else Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv")) in
    Driver.load_driver env s []


let do_global_theory (tname,p,t) =
  let format = Opt.get_def "why" !opt_parser in
  let th = try Env.read_theory ~format env p t with Env.TheoryNotFound _ ->
    eprintf "Theory '%s' not found.@." tname;
    exit 1
  in
  let task = Task.use_export None th in
  let dest = Driver.file_of_theory opt_driver "lib" th in
  let file = Filename.concat opt_output dest in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  Driver.print_task ?old opt_driver (formatter_of_out_channel cout) task;
  close_out cout

let () =
  try
    Queue.iter do_global_theory opt_queue
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
