(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Wstdlib
open Pmodule
open Compile
open Theory

let usage_msg = sprintf
    "Usage: %s [options] -D <driver> [<file>.<Module>*.<symbol>?|-]\n\
     Extract some WhyML code to the target language.\n"
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

type recurs_single = RecursiveDeps | Recursive | Single
let opt_rec_single = ref Single

type flat_modular = Flat | Modular
let opt_modu_flat = ref Flat

let is_uppercase = Strings.char_is_uppercase
let opt_interface = ref false

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

let option_list =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    Key ('D', "driver"), Hnd1 (AString, fun s -> opt_driver := s::!opt_driver),
    "<file> specify an extraction driver";
    KLong "recursive", Hnd0 (fun () -> opt_rec_single := Recursive),
    " recursively extract dependencies, including used\nmodules";
    KLong "recursive-deps", Hnd0 (fun () -> opt_rec_single := RecursiveDeps),
    " recursively extract all program dependencies";
    KLong "flat", Hnd0 (fun () -> opt_modu_flat := Flat),
    " perform a flat extraction (default)";
    KLong "modular", Hnd0 (fun () -> opt_modu_flat := Modular),
    " perform a modular extraction";
    KLong "interface", Hnd0 (fun () -> opt_interface := true),
    " also extract interface files (requires modular\nextraction)";
    Key ('o', "output"), Hnd1 (AString, fun s -> opt_output := Some s),
    "<file|dir> destination of extracted code";
  ]

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
      eprintf
        "Option '-o' should be given an existing directory as argument.@.";
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
      let tname = m.mod_theory.th_name.Ident.id_string in
      Debug.dprintf Pdriver.debug
        "extract module %s to standard output@." tname;
      stdout, None
  | Some f ->
      let file = Filename.concat f (fg ?fname m) in
      let tname = m.mod_theory.th_name.Ident.id_string in
      Debug.dprintf Pdriver.debug "extract module %s to file %s@." tname file;
      let old = if Sys.file_exists file then begin
          let backup = file ^ ".bak" in
          Sys.rename file backup;
          Some (open_in backup) end else None in
      open_out file, old

let pmod_name pm = pm.mod_theory.th_name

let compute_preludes id_th pm deps epm =
  let ht = Hstr.create 8 in
  let add l s = if Hstr.mem ht s then l else (Hstr.add ht s (); s :: l) in
  let th_epm dep = Ident.Mid.find_def [] (pmod_name dep) epm in
  let add_tps acc dep = List.fold_left add acc (List.rev (th_epm dep)) in
  (* exported preludes from deps *)
  let epl = List.fold_left add_tps [] deps in
  (* prelude of current module *)
  let mpl = List.fold_left add []
              (List.rev (Ident.Mid.find_def [] id_th pm)) in
  epl@mpl

let export_deps = Ident.Hid.create 16
let trivial_files = Ident.Hid.create 16

let add_dep dep (ds, dl) =
  let id = pmod_name dep in
  if Ident.Sid.mem id ds then (ds, dl)
  else (Ident.Sid.add id ds, dep::dl)

let add_export_dep (ds, dl) pm =
  let open Ident in
  let dep = pmod_name pm in
  let (_, depl) = Hid.find_def export_deps (Sid.empty, []) dep in
  let (ds, dl) = List.fold_right add_dep depl (ds, dl) in
  add_dep pm (ds, dl)

let print_mdecls ?fname m mdecls alldeps =
  let open Pdriver in
  let nontrivialdeps =
    List.filter (fun pm -> not (Ident.Hid.mem trivial_files (pmod_name pm)))
      alldeps in
  let tname = m.mod_theory.th_name in
  let pargs, printer = lookup_printer opt_driver in
  let test_decl_not_driver decl =
    let decl_name = Mltree.get_decl_name decl in
    let test_id_not_driver id =
      Printer.query_syntax pargs.Pdriver.syntax id = None in
    List.exists test_id_not_driver decl_name in
  let prelude_exists =
    Ident.Mid.mem m.mod_theory.th_name pargs.thprelude
    || (!opt_interface && Ident.Mid.mem tname pargs.thinterface)
  in
  let exported_prelude_exists =
    Ident.Mid.mem tname pargs.thexportpre
    || Ident.Mid.mem tname pargs.thexportint in
  if Ident.Sid.mem tname opt_driver.drv_noextract
  then begin
    Ident.Hid.add trivial_files tname ();
    exported_prelude_exists
  end else if List.exists test_decl_not_driver mdecls || prelude_exists
  then begin
    let implem =
      if opt_modu_flat = Flat
      then printer.flat_printer
      else printer.implem_printer in
    let cout, old = get_cout_old implem.filename_generator m ?fname in
    let fmt = formatter_of_out_channel cout in
    implem.header_printer pargs ?old ?fname fmt m;
    (* print_preludes *)
    let pm = pargs.thprelude in
    let epm = pargs.thexportpre in
    let pl = compute_preludes tname pm alldeps epm in
    implem.prelude_printer pargs ?old ?fname ~deps:nontrivialdeps
      ~global_prelude:pargs.prelude
      ~prelude:pl fmt m ;
    (* print decls *)
    let pr_decl fmt d =
      implem.decl_printer pargs ?old ?fname m fmt d in
    Pp.print_list Pp.nothing pr_decl fmt mdecls;
    implem.footer_printer pargs ?old ?fname fmt m;
    if cout <> stdout then close_out cout;
    (* print interface file *)
    if !opt_interface then begin
      match printer.interf_printer with
      | None ->
          eprintf "Driver does not support interface extraction.@.";
          exit 1
      | Some interf ->
          let iout, old = get_cout_old interf.filename_generator m ?fname in
          let ifmt = formatter_of_out_channel iout in
          interf.header_printer pargs ?old ?fname ifmt m;
          (* print interfaces *)
          let im = pargs.thinterface in
          let eim = pargs.thexportint in
          let il = compute_preludes tname im alldeps eim in
          interf.prelude_printer pargs ?old ?fname ~deps:nontrivialdeps
            ~global_prelude:pargs.prelude
            ~prelude:il
            ifmt m;
          (* print decls *)
          let pr_idecl fmt d =
            interf.decl_printer pargs ?old ?fname m fmt d in
          Pp.print_list Pp.nothing pr_idecl ifmt mdecls;
          interf.footer_printer pargs ?old ?fname ifmt m;
          if iout <> stdout then close_out iout end;
    true end
  else
    if exported_prelude_exists
    then begin
      Ident.Hid.add trivial_files (pmod_name m) ();
      true
    end
    else false

let find_module_path mm path m = match path with
  | [] -> Mstr.find m mm
  | path -> let mm = Env.read_library Pmodule.mlw_language env path in
      Mstr.find m mm

let find_module_id mm id =
  let (path, m, _) = Pmodule.restore_path id in find_module_path mm path m

let visited = Ident.Hid.create 1024

let translate_module =
  let memo = Ident.Hid.create 16 in
  fun m ->
    let name = m.mod_theory.th_name in
    try Ident.Hid.find memo name with Not_found ->
      let pm = Translate.module_ m in
      let pm = Transform.module_ pm in
      Ident.Hid.add memo name pm;
      pm

(* let not_extractable_theories = ["why3"; "map"; ] *)

(* let is_not_extractable_theory = *)
(*   let h = Hstr.create 16 in *)
(*   List.iter (fun s -> Hstr.add h s ()) not_extractable_theories; *)
(*   Hstr.mem h *)

let translate ?decl m = match decl with
  | None   -> (translate_module m).Mltree.mod_decl
  | Some d -> Translate.pdecl_m m d

let extract_to =
  let memo = Ident.Hid.create 16 in
  fun ?fname ?decl m use use_export ->
  match m.mod_theory.th_path with
  | "why3"::_ -> false
  | _ ->
     let name = m.mod_theory.th_name in
     if not (Ident.Hid.mem memo name) then begin
         (* compute exported dependencies of m *)
         let empty_deps = Ident.Sid.empty, [] in
         let ex_deps = List.fold_left add_export_dep empty_deps use_export in
         Ident.Hid.replace export_deps name ex_deps;
         (* indirect dependencies are the exported deps of the direct deps *)
         let ind_deps =
           List.fold_left
             (fun acc ddep ->
               (snd (Ident.Hid.find export_deps (pmod_name ddep)))
               @ acc)
             []
             use in
         let deps = use @ ind_deps @ snd ex_deps in
         (* translate and print m *)
         let mdecls = translate ?decl m in
         let file_exists = print_mdecls ?fname m mdecls deps in
         Ident.Hid.add memo name file_exists;
         file_exists end
     else Ident.Hid.find memo name

let rec use_fold toplevel f l =
  List.fold_left
    (fun (use, use_export)
     -> function | Uuse t ->
                    if f t
                    then if toplevel then (use, t::use_export)
                         else (t::use, use_export)
                    else use, use_export
                 | Uscope (_,l) ->
                    let use', _ = use_fold false f l in
                    use'@use, use_export
                 | _ -> use, use_export) ([], []) l

let find_decl mm id =
  let m = find_module_id mm id in
  let m = translate_module m in
  Ident.Mid.find id m.Mltree.mod_known

let rec do_extract_module ?fname in_deps m =
  let extract_use m' =
    let fname = if m'.mod_theory.Theory.th_path = [] then fname else None in
    do_extract_module ?fname in_deps m' in
  let deps_and_use ({mod_theory = {th_name}} as m') =
    in_deps th_name && extract_use m' in
  let use, use_export = match opt_rec_single with
    | Recursive -> use_fold true extract_use m.mod_units
    | RecursiveDeps -> use_fold true deps_and_use m.mod_units
    | Single -> [], [] in
  extract_to ?fname m use use_export

let do_extract_module ?fname m =
  let visited_mod = Ident.Hid.create 128 in
  let recurs = opt_rec_single = RecursiveDeps in
  let th_name = m.mod_theory.th_name in
  let visit_id_deps id =
    if not (Ident.Hid.mem visited id) then try
      let (path, str_m, _) = Pmodule.restore_path id in
      let m = find_module_path Mstr.empty path str_m in
      Ident.Hid.add visited_mod m.mod_theory.th_name ();
      Ident.Hid.add visited id ();
    with Not_found -> () in
  (* compute dependencies of current module [m] *)
  if recurs then begin try
    Ident.Hid.add visited_mod th_name ();
    let m = translate_module m in
    List.iter (fun d -> Mltree.iter_deps visit_id_deps d) m.Mltree.mod_decl;
  with Not_found -> () end;
  do_extract_module ?fname (Ident.Hid.mem visited_mod) m

let find_pmod m mlw_file fname =
  try Mstr.find m mlw_file with Not_found ->
    eprintf "Module '%s' not found in the file '%s'.@." m fname;
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

let find_pdecl m s =
  let ns = m.mod_export in
  let id = find_symbol_id ns s in
  Ident.Mid.find id m.mod_known

let do_extract_symbol_from ?fname m str_symbol =
  (* FIXME: recursively extract modules also in this case *)
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
      let do_m _ m = ignore (do_extract_module ~fname m) in
      Mstr.iter do_m mm
  | Module (path, m) ->
      let mm = Mstr.empty in
      let m = find_module_path mm path m in
      ignore (do_extract_module m)
  | Symbol (path, m, s) ->
      let mm = Mstr.empty in
      let m = find_module_path mm path m in
      ignore (do_extract_symbol_from m s [] []) (* FIXME empty deps ? *)

type extract_info = {
  info_rec : bool;
  info_id  : Ident.ident;
}

let toextract = ref []

let rec visit ~recurs mm id =
  if not (Ident.Hid.mem visited id) then begin try
    let (path_th, _, _) = Pmodule.restore_path id in
    match path_th with
    (* this test avoids symbols from the Why3's standard library (e.g. Tuples_n)
       to get extracted *)
    | "why3"::_ -> ()
    | _ -> let d = find_decl mm id in
        Ident.Hid.add visited id ();
        if recurs then Mltree.iter_deps (visit ~recurs mm) d;
        toextract := { info_rec = recurs; info_id = id } :: !toextract
  with Not_found -> () end

let flat_extraction mm = function
  | File fname ->
      let format = !opt_parser in
      let mmf = read_mlw_file ?format env fname in
      let do_m s m mm =
        if Mstr.mem s mm then begin
          eprintf "multiple module '%s'; use -L . instead@." s;
          exit 1 end;
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
    | Flat ->
        let open Pdriver in
        let mm = Queue.fold flat_extraction Mstr.empty opt_queue in
        let (pargs, printer) = lookup_printer opt_driver in
        let flat_printer = printer.flat_printer in
        let cout = match opt_output with
          | None -> stdout
          | Some file -> open_out file in
        let fmt = formatter_of_out_channel cout in
        let thprelude = pargs.thprelude in
        let thexportpre = pargs.thexportpre in
        let prs = Hstr.create 16 in
        let print_prelude sl =
          List.iter
            (fun s ->
              if not (Hstr.mem prs s)
              then begin
                  Hstr.add prs s ();
                  fprintf fmt "%s@\n@." s
                end)
            sl
        in
        let rec do_preludes id =
          (try
             let m = find_module_id mm id in
             Ident.Sid.iter do_preludes m.mod_used
           with Not_found -> ());
          let pl = Ident.Mid.find_def [] id thprelude in
          let ipl = Ident.Mid.find_def [] id thexportpre in
          print_prelude pl;
          print_prelude ipl;
        in
        print_prelude pargs.prelude;
        let visit_m _ m =
          do_preludes m.mod_theory.th_name;
          let tm = translate_module m in
          let visit_id id _ = visit ~recurs:true mm id in
          Ident.Mid.iter visit_id tm.Mltree.mod_known;
        in
        Mstr.iter visit_m mm;
        let extract fmt { info_id = id } =
          let pm = find_module_id mm id in
          let m = translate_module pm in
          let d = Ident.Mid.find id m.Mltree.mod_known in
          flat_printer.decl_printer pargs pm fmt d in
        let idl = List.rev !toextract in
        let is_local { info_id = id; info_rec = r } =
          let (path, m, _) = Pmodule.restore_path id in
          path = [] || Mstr.mem m mm || not r in
        let idl = match opt_rec_single with
          | Single -> List.filter is_local idl
          | Recursive | RecursiveDeps -> idl in
        Pp.print_list Pp.nothing extract fmt idl;
        if cout <> stdout then close_out cout
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
