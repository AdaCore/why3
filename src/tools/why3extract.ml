(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
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
  "Usage: %s [options] -D <driver> [-o <dir|file>] \
             [<file>.<Module>*.<symbol>?|-]"
  (Filename.basename Sys.argv.(0))

type extract_target =
  | File   of string
  | Module of string list * string
  | Symbol of string list * string * string

let opt_queue = Queue.create ()

(* let opt_input = ref None *)

let opt_parser = ref None
let opt_output = ref None
let opt_driver = ref []

type recurs_single = Recursive | Single
let opt_rec_single = ref Single

type flat_modular = Flat | Modular
let opt_modu_flat = ref Flat

let is_uppercase = Strings.char_is_uppercase

let add_opt_file x =
  let invalid_path () = Format.eprintf "invalid path: %s@." x; exit 1 in
  let target =
    if Sys.file_exists x then File x else
      let path = Strings.split '.' x in
      if path = [] then invalid_path ();
      let path, s = Lists.chop_last path in
      if String.length s = 0 then invalid_path ();
      if is_uppercase s.[0] then Module (path, s) else
      begin
        if path = [] then invalid_path ();
        let path, m = Lists.chop_last path in
        Symbol (path, m, s)
      end in
  Queue.push target opt_queue

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
  "--recursive", Arg.Unit (fun () -> opt_rec_single := Recursive),
      " recursively extract all dependencies";
  "--flat", Arg.Unit (fun x -> x),
      " perform a flat extraction (default option)";
  "--modular", Arg.Unit (fun () -> opt_modu_flat := Modular),
      " perform a modular extraction";
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

let opt_modu_flat  = !opt_modu_flat
let opt_rec_single = !opt_rec_single

let opt_output = match opt_modu_flat, !opt_output with
  | Modular, None ->
    eprintf "Output directory (-o) is required for modular extraction.@.";
    exit 1
  | Modular, Some s when not (Sys.file_exists s) ->
    eprintf "Option '-o' should be given an existing directory as argument.@.";
    exit 1
  | Modular, Some s when not (Sys.is_directory s) ->
    eprintf "Option '-o' should be given a directory as argument.@.";
    exit 1
  | Flat, Some s when Sys.file_exists s && Sys.is_directory s ->
    eprintf "Option '-o' should be given a file as argument.@.";
    exit 1
  | Modular, Some _ | Flat, None | Flat, Some _ -> !opt_output

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

let get_cout_old ?fname fg m = match opt_output with
  | None ->
    let tname = m.mod_theory.Theory.th_name.Ident.id_string in
    Debug.dprintf Pdriver.debug "extract module %s to standard output@." tname;
    stdout, None
  | Some f ->
    let file = Filename.concat f (fg ?fname m) in
    let tname = m.mod_theory.Theory.th_name.Ident.id_string in
    Debug.dprintf Pdriver.debug "extract module %s to file %s@." tname file;
    let old = if Sys.file_exists file then begin
      let backup = file ^ ".bak" in
      Sys.rename file backup;
      Some (open_in backup) end else None in
    open_out file, old

let print_preludes =
  let ht = Hstr.create 8 in
  let add l s = if Hstr.mem ht s then l else (Hstr.add ht s (); s :: l) in
  fun id_th fmt pm ->
    let th_pm = Ident.Mid.find_def [] id_th pm in
    let l = List.fold_left add [] th_pm in
    Printer.print_prelude fmt l

let print_mdecls ?fname m mdecls =
  let (fg,pargs,pr) = Pdriver.lookup_printer opt_driver in
  let test_decl_not_driver decl =
    let decl_name = Mltree.get_decl_name decl in
    let test_id_not_driver id =
      Printer.query_syntax pargs.Pdriver.syntax id = None in
    List.exists test_id_not_driver decl_name in
  if List.exists test_decl_not_driver mdecls then begin
    let cout, old = get_cout_old fg m ?fname in
    let fmt = formatter_of_out_channel cout in
    (* print driver prelude *)
    let pm = pargs.Pdriver.thprelude in
    print_preludes m.mod_theory.Theory.th_name fmt pm;
    let flat = opt_modu_flat = Flat in
    let pr_decl fmt d = fprintf fmt "%a" (pr pargs ?old ?fname ~flat m) d in
    Pp.print_list Pp.nothing pr_decl fmt mdecls;
    if cout <> stdout then close_out cout end

let find_module_path mm path m = match path with
  | [] -> Mstr.find m mm
  | path -> let mm = Env.read_library Pmodule.mlw_language env path in
    Mstr.find m mm

let find_module_id mm id =
  let (path, m, _) = Pmodule.restore_path id in find_module_path mm path m

let translate_module =
  let memo = Ident.Hid.create 16 in
  fun m ->
    let name = m.mod_theory.Theory.th_name in
    try Ident.Hid.find memo name with Not_found ->
      let pm = Translate.module_ m in
      let pm = Transform.module_ pm in
      Ident.Hid.add memo name pm;
      pm

let not_extractable_theories = ["why3"; "map"; "seq"; ]

let is_not_extractable_theory =
  let h = Hstr.create 16 in
  List.iter (fun s -> Hstr.add h s ()) not_extractable_theories;
  Hstr.mem h

let extract_to =
  let memo = Ident.Hid.create 16 in
  fun ?fname ?decl m ->
    match m.mod_theory.Theory.th_path with
    | t::_ when is_not_extractable_theory t -> ()
    | _ -> let name = m.mod_theory.Theory.th_name in
        if not (Ident.Hid.mem memo name) then begin
          Ident.Hid.add memo name ();
          let mdecls = match decl with
            | None   -> (translate_module m).Mltree.mod_decl
            | Some d -> Translate.pdecl_m m d in
          print_mdecls ?fname m mdecls
        end

let rec use_iter f l =
  List.iter
    (function Uuse t -> f t | Uscope (_,l) -> use_iter f l | _ -> ()) l

let rec do_extract_module ?fname m =
  let extract_use m' =
    let fname =
      if m'.mod_theory.Theory.th_path = [] then fname else None in
    do_extract_module ?fname m'
  in
  begin match opt_rec_single with
  | Recursive -> use_iter extract_use m.mod_units
  | Single -> ()
  end;
  extract_to ?fname m

let do_extract_module_from fname mm m =
  try
    let m = Mstr.find m mm in do_extract_module ~fname m
  with Not_found ->
    eprintf "Module '%s' not found in file '%s'.@." m fname;
    exit 1

let get_symbol ns find str_symbol =
  try let symbol = find ns [str_symbol] in Some symbol
  with Not_found -> None

let find_symbol_id ns str_symbol =
  match get_symbol ns ns_find_rs str_symbol with
    | Some rs -> rs.Expr.rs_name
    | None -> (* creative indentation *)
    begin match get_symbol ns ns_find_its str_symbol with
    | Some its -> its.Ity.its_ts.Ty.ts_name
    | None -> (* creative indentation *)
    begin match get_symbol ns ns_find_xs str_symbol with
    | Some xs -> xs.Ity.xs_name
    | None -> raise Not_found
    end end

let find_pmod m mlw_file fname =
  try Mstr.find m mlw_file with Not_found ->
    eprintf "Module '%s' not found in the file '%s'.@." m fname;
    exit 1

let find_pdecl m s =
  let ns = m.mod_export in
  let id = find_symbol_id ns s in
  Ident.Mid.find id m.mod_known

let do_extract_symbol_from ?fname m str_symbol =
  let decl = find_pdecl m str_symbol in
  extract_to ?fname ~decl m

let read_mlw_file ?format env fname =
  let cin = open_in fname in
  let mm = Env.read_channel ?format mlw_language env fname cin in
  close_in cin;
  mm

let do_modular target =
  let format = !opt_parser in
  match target with
  | File fname ->
    let mm = read_mlw_file ?format env fname in
    let do_m _ m = do_extract_module ~fname m in
    Mstr.iter do_m mm
  | Module (path, m) ->
    let mm = Mstr.empty in
    let m = find_module_path mm path m in
    do_extract_module m
  | Symbol (path, m, s) ->
    let mm = Mstr.empty in
    let m = find_module_path mm path m in
    do_extract_symbol_from m s

type extract_info = {
  info_rec : bool;
  info_id  : Ident.ident;
}

let visited = Ident.Hid.create 1024
let toextract = ref []

let find_decl mm id =
  let m = find_module_id mm id in
  let m = translate_module m in
  Ident.Mid.find id m.Mltree.mod_known

let rec visit ~recurs mm id =
  if not (Ident.Hid.mem visited id) then begin try
      let d = find_decl mm id in
      Ident.Hid.add visited id ();
      if recurs then Mltree.iter_deps (visit ~recurs mm) d;
      toextract := { info_rec = recurs; info_id = id } :: !toextract
    with Not_found -> ()
  end

let flat_extraction mm = function
  | File fname ->
    let format = !opt_parser in
    let mmf = read_mlw_file ?format env fname in
    let do_m s m mm =
      if Mstr.mem s mm then begin
        eprintf "multiple module '%s'; use -L . instead@." s;
        exit 1
      end;
      Mstr.add s m mm in
    Mstr.fold do_m mmf mm
  | Module (path, ms) ->
    let m = find_module_path mm path ms in (* FIXME: catch Not_found here *)
    let m_t = translate_module m in
    let recurs = opt_rec_single = Recursive in
    Ident.Mid.iter (fun id _ -> visit ~recurs mm id) m_t.Mltree.mod_known;
    Mstr.add ms m mm
  | Symbol (path, ms, s) ->
    let m = find_module_path mm path ms in
    let ns = m.mod_export in
    let id = find_symbol_id ns s in
    let recurs = opt_rec_single = Recursive in
    visit ~recurs mm id;
    (* Mstr.add ms m  *)mm

let () =
  try
    match opt_modu_flat with
    | Modular -> Queue.iter do_modular opt_queue
    | Flat -> let mm = Queue.fold flat_extraction Mstr.empty opt_queue in
      let (_fg, pargs, pr) = Pdriver.lookup_printer opt_driver in
      let cout = match opt_output with
        | None -> stdout
        | Some file -> open_out file in
      let fmt = formatter_of_out_channel cout in
      let thprelude = pargs.Pdriver.thprelude in
      let print_prelude = List.iter (fun s -> fprintf fmt "%s@\n@." s) in
      let rec do_preludes id =
        (try
          let m = find_module_id mm id in
          Ident.Sid.iter do_preludes m.mod_used
        with Not_found -> ());
        print_preludes id fmt thprelude
      in
      print_prelude pargs.Pdriver.prelude;
      let visit_m _ m =
        do_preludes m.mod_theory.Theory.th_name;
        let tm = translate_module m in
        let visit_id id _ = visit ~recurs:true mm id in
        Ident.Mid.iter visit_id tm.Mltree.mod_known;
      in
      Mstr.iter visit_m mm;
      let extract fmt { info_id = id } =
        let pm = find_module_id mm id in
        let m = translate_module pm in
        let d = Ident.Mid.find id m.Mltree.mod_known in
        pr pargs ~flat:true pm fmt d in
      let idl = List.rev !toextract in
      let is_local { info_id = id; info_rec = r } =
        let (path, m, _) = Pmodule.restore_path id in
        path = [] || Mstr.mem m mm || not r in
      let idl = match opt_rec_single with
        | Single -> List.filter is_local idl
        | Recursive -> idl in
      Pp.print_list Pp.nothing extract fmt idl;
      if cout <> stdout then close_out cout
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
