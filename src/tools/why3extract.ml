(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Stdlib
open Pmodule

let usage_msg = sprintf
  "Usage: %s [options] -D <driver> -o <dir> [[file|-] [-T <theory>]...]..."
  (Filename.basename Sys.argv.(0))

let opt_queue = Queue.create ()

let opt_input = ref None

let add_opt_file x =
  let tlist = Queue.create () in
  Queue.push (Some x, tlist) opt_queue;
  opt_input := Some tlist

(* TODO : rename theory into module, -T into -M *)
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
      Queue.push (x, p, t) tlist
  | _ ->
      let tlist = Queue.create () in
      Queue.push (None, tlist) opt_queue;
      opt_input := None;
      Queue.push (x, p, t) tlist

let opt_parser = ref None
let opt_output = ref None
let opt_driver = ref []

let option_list = [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " read the input file from stdin";
  "-T", Arg.String add_opt_theory,
      "<theory> select <theory> in the input file or in the library";
  "--theory", Arg.String add_opt_theory,
      " same as -T";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-D", Arg.String (fun s -> opt_driver := s::!opt_driver),
      "<file> specify an extraction driver";
  "--driver", Arg.String (fun s -> opt_driver := s::!opt_driver),
      " same as -D";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> print the selected goals to separate files in <dir>";
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

let driver_file s =
  if Sys.file_exists s || String.contains s '/' || String.contains s '.' then s
  else Filename.concat Config.datadir (Filename.concat "drivers" (s ^ ".drv"))

let opt_driver =
  try match List.rev_map driver_file !opt_driver with
  | [] ->
    eprintf "Extraction driver (-D) is required.@.";
    exit 1
  | f::ef ->
    Pdriver.load_driver env f ef
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let extract_to ?fname m =
  let (fg,pargs,pr) = Pdriver.lookup_printer opt_driver in
  let file = Filename.concat opt_output (fg ?fname m) in
  let old =
    if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup)
    end else None in
  let cout = open_out file in
  let fmt = formatter_of_out_channel cout in
  let tname = m.mod_theory.Theory.th_name.Ident.id_string in
  Debug.dprintf Pdriver.debug "extract module %s to file %s@." tname file;
  pr ?old pargs fmt m;
  close_out cout

let extract_to =
  let visited = Ident.Hid.create 17 in
  fun ?fname m ->
    let name = m.mod_theory.Theory.th_name in
    if not (Ident.Hid.mem visited name) then begin
      Ident.Hid.add visited name ();
      extract_to ?fname m
    end

let rec use_iter f l =
  List.iter (function Uuse t -> f t | Uscope (_,_,l) -> use_iter f l | _ -> ()) l

let rec do_extract_module ?fname m =
  let extract_use m' =
    let fname =
      if m'.mod_theory.Theory.th_path = [] then fname else None
    in
    do_extract_module ?fname m'
  in
  use_iter extract_use m.mod_units;
  extract_to ?fname m

let do_global_extract (_,p,t) =
  let env = opt_driver.Pdriver.drv_env in
  let m = read_module env p t in
  do_extract_module m


let do_extract_module_from fname mm (tname,_,t) =
  try
    let m = Mstr.find t mm in do_extract_module ~fname m
  with Not_found ->
    eprintf "Module '%s' not found in file '%s'.@." tname fname;
    exit 1

let do_local_extract fname cin tlist =
  let env = opt_driver.Pdriver.drv_env in
  let format = !opt_parser in
  let mm =
    Env.read_channel ?format mlw_language env fname cin in
  if Queue.is_empty tlist then
    let do_m _ m = do_extract_module ~fname m in
    Mstr.iter do_m mm
  else
    Queue.iter (do_extract_module_from fname mm) tlist

let do_input = function
  | None, tlist ->
    Queue.iter do_global_extract tlist
  | Some f, tlist ->
    let fname, cin = match f with
      | "-" -> "stdin", stdin
      | f   -> f, open_in f in
    do_local_extract fname cin tlist;
    close_in cin

let () =
  try
    Queue.iter do_input opt_queue;
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
