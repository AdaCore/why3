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

let opt_input = ref None

let add_opt_file x =
  let target = match Strings.split '.' x with
  | [f]     -> File f
  | [f;m]   -> Module (f, m)
  | [f;m;s] -> Symbol (f, m, s)
  | _ -> Format.eprintf "Invalid input argument@."; exit 1 in
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
  if Queue.is_empty opt_queue then
    Whyconf.Args.exit_with_usage option_list usage_msg

let opt_recurs = !opt_recurs

type output = Empty | Dir of string

let get_output = function Empty -> assert false | Dir s -> s

(* FIXME: accept --mono without -o and use to standard output *)
let opt_output =
  match !opt_output with
  | None   -> Empty
  | Some d -> Dir d

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
  let info = {
    Translate.info_current_mo   = Some m;
    Translate.info_mo_known_map = m.mod_known;
  } in
  let mdecls = Translate.module_ info m in
  let mdecls = Transform.module_ info mdecls.ML.mod_decl in
  match opt_recurs with
  | Single ->
    let file = Filename.concat (get_output opt_output) (fg ?fname m) in
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
    List.iter (pr ?old ?fname pargs m fmt) mdecls;
    close_out cout
  | Recursive -> assert false (*TODO*)

let extract_to =
  let visited = Ident.Hid.create 17 in
  fun ?fname m ->
    let name = m.mod_theory.Theory.th_name in
    if not (Ident.Hid.mem visited name) then begin
      Ident.Hid.add visited name ();
      extract_to ?fname m
    end

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

let do_extract_symbol_from fname mm m s = () (*TODO*)

let do_local_extract target =
  let env = opt_driver.Pdriver.drv_env in
  let format = !opt_parser in
  match target with
  | File fname ->
    let cin = open_in fname in
    let mm = Env.read_channel ?format mlw_language env fname cin in
    let do_m _ m = do_extract_module ~fname m in
    Mstr.iter do_m mm;
    close_in cin
  | Module (fname, m) ->
    let cin = open_in fname in
    let mm = Env.read_channel ?format mlw_language env fname cin in
    do_extract_module_from fname mm m;
    close_in cin
  | Symbol (fname, m, s) ->
    let cin = open_in fname in
    let mm = Env.read_channel ?format mlw_language env fname cin in
    do_extract_symbol_from fname mm m s;
    close_in cin

let do_input = function
  | None -> assert false (*TODO*)
    (* Queue.iter do_global_extract tlist *)
  | Some target -> do_local_extract target

(*
let visited = Hid.create 1024
let toextract = ref []

let rec visit id =
  if not (Hid.mem id visited) then begin
    let d = Hid.find Compile.knownmap id in
    ML.iter_deps visit d;
    Hid.add visited id ();
    toextract := id :: !toextract
  end

let monolithic () =
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
    (* begin match opt_recurs with *)
    (* | Monolithic -> (\* monolithic () *\) assert false (\*TODO*\) *)
    (* | Recursive | SingleModule -> () end *)
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3extract.opt"
End:
*)
