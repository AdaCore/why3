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
open Compile

let usage_msg = sprintf
  "Usage: %s [options] -D <driver> -o <dir> [[file|-] [-T <theory>]...]..."
  (Filename.basename Sys.argv.(0))

type extract_target =
  | File   of string
  | Module of string * string
  | Symbol of string * string * string

let opt_queue = Queue.create ()

(* let opt_input = ref None *)

let add_opt_file x =
  let target =
    if Sys.file_exists x then File x else match Strings.split '.' x with
      | [f;m]   -> Module (f, m)
      | [f;m;s] -> Symbol (f, m, s)
      | _ -> Format.eprintf "Invalid input argument.@."; exit 1 in
  Queue.push (Some target) opt_queue

let opt_parser = ref None
let opt_output = ref None
let opt_driver = ref []
type extraction_mode = Recursive | Single
let opt_recurs = ref Single

let option_list = [
  "-", Arg.Unit (fun () -> add_opt_file "-"),
      " read the input file from stdin";
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
  "-D", Arg.String (fun s -> opt_driver := s::!opt_driver),
      "<file> specify an extraction driver";
  "--driver", Arg.String (fun s -> opt_driver := s::!opt_driver),
      " same as -D";
  "--recursive", Arg.Unit (fun () -> opt_recurs := Recursive),
      " perform a recursive extraction";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<file|dir> destination of extracted code";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o" ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

let () =
  if Queue.is_empty opt_queue then begin
    Whyconf.Args.exit_with_usage option_list usage_msg
  end

let opt_recurs = !opt_recurs

(* FIXME: accept --mono without -o and use to standard output *)
let opt_output = !opt_output

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

let print_mdecls ?fname m mdecls =
  let (fg,pargs,pr) = Pdriver.lookup_printer opt_driver in
  let cout, old = match opt_output with
    | None ->
      let tname = m.mod_theory.Theory.th_name.Ident.id_string in
      Debug.dprintf Pdriver.debug "extract module %s to standard output" tname;
      stdout, None
    | Some f ->
      let file = Filename.concat f (fg ?fname m) in
      let tname = m.mod_theory.Theory.th_name.Ident.id_string in
      Debug.dprintf Pdriver.debug "extract module %s to file %s@." tname file;
      let old = if Sys.file_exists file then begin
          let backup = file ^ ".bak" in
          Sys.rename file backup;
          Some (open_in backup) end else None in
      open_out file, old in
  let fmt = formatter_of_out_channel stdout in
  let recursive = opt_recurs = Recursive in
  List.iter (pr pargs ?old ?fname recursive m fmt) mdecls;
  if cout <> stdout then close_out cout

let translate_module =
  let memo = Ident.Hid.create 16 in
  fun m ->
    let name = m.mod_theory.Theory.th_name in
    try Ident.Hid.find memo name with Not_found ->
      let pm, info = Translate.module_ m in
      let pm       = Transform.module_ info pm in
      Ident.Hid.add memo name pm;
      pm

let extract_to ?fname ?decl m =
  let mdecls = match decl with
    | None -> (translate_module m).ML.mod_decl
    | Some d -> List.map fst (Translate.pdecl_m m d) in
  print_mdecls ?fname m mdecls

let rec use_iter f l =
  List.iter
    (function Uuse t -> f t | Uscope (_,_,l) -> use_iter f l | _ -> ()) l

let rec do_extract_module ?fname m =
  let extract_use m' =
    let fname =
      if m'.mod_theory.Theory.th_path = [] then fname else None
    in
    do_extract_module ?fname m'
  in
  begin match opt_recurs with
  | Recursive -> use_iter extract_use m.mod_units
  | Single -> ()
  end;
  extract_to ?fname m

(* let do_global_extract (_,p,t) = *)
(*   let env = opt_driver.Pdriver.drv_env in *)
(*   let m = read_module env p t in *)
(*   do_extract_module m *)

let do_extract_module_from fname mm m =
  try
    let m = Mstr.find m mm in do_extract_module ~fname m
  with Not_found ->
    eprintf "Module '%s' not found in file '%s'.@." m fname;
    exit 1

let get_symbol ns find str_symbol =
  try let symbol = find ns [str_symbol] in Some symbol
  with Not_found -> None

let do_extract_symbol_from fname mlw_file m str_symbol =
  let pmod =
    try Mstr.find m mlw_file with Not_found ->
      eprintf "Module '%s' not found in the file '%s'.@." m fname;
      exit 1 in
  let ns = pmod.mod_export in
  let id = match get_symbol ns ns_find_rs str_symbol with
    | Some rs -> rs.Expr.rs_name
    | None -> (* creative indentation *)
    begin match get_symbol ns ns_find_its str_symbol with
    | Some its -> its.Ity.its_ts.Ty.ts_name
    | None -> (* creative indentation *)
    begin match get_symbol ns ns_find_xs str_symbol with
    | Some xs -> xs.Ity.xs_name
    | None ->
      eprintf "Symbol '%s' not found in module '%s' of file '%s'.@."
        str_symbol m fname;
      exit 1
    end end in
  let decl = Ident.Mid.find id pmod.mod_known in
  extract_to ~fname ~decl pmod

let read_mlw_file ?format env fname =
  let cin = open_in fname in
  let mm = Env.read_channel ?format mlw_language env fname cin in
  close_in cin;
  mm

let do_local_extract target =
  let env = opt_driver.Pdriver.drv_env in
  let format = !opt_parser in
  match target with
  | File fname ->
    let mm = read_mlw_file ?format env fname in
    let do_m _ m = do_extract_module ~fname m in
    Mstr.iter do_m mm
  | Module (fname, m) ->
    let fname = fname ^ ".mlw" in
    let mm = read_mlw_file ?format env fname in
    do_extract_module_from fname mm m
  | Symbol (fname, m, s) ->
    let fname = fname ^ ".mlw" in
    let mm = read_mlw_file ?format env fname in
    do_extract_symbol_from fname mm m s

let do_input = function
  | None -> assert false (*TODO*)
    (* Queue.iter do_global_extract tlist *)
  | Some target ->
    do_local_extract target

(*
let visited = Hid.create 1024
let toextract = ref []

let rec visit id =
  if not (Hid.mem id visited) then begin
    let p = restore_path id in
    let m = ... module Why3 ... in
    let m = translate_module m in
    let d = Hid.find m.mod_known id in
    ML.iter_deps visit d;
    Hid.add visited id ();
    toextract := id :: !toextract
  end

let flat_extraction () =
  (* TODO call visit on all ids to extract *)
  let (fg,pargs,pr) = Pdriver.lookup_printer opt_driver in
  let extract id =
    let d = Hid.find Compile.knownmap id in in
    pr pargs d in
  List.iter extract !toextract
*)

let () =
  try
    Queue.iter do_input opt_queue;
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3extract.opt"
End:
*)
