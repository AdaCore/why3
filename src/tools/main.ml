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
open Whyconf
open Theory

let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_attrs = ref false

let option_list =
  let open Getopt in
  Args.common_options @
  [ KLong "list-transforms", Hnd0 (fun () -> opt_list_transforms := true),
    " list known transformations";
    KLong "list-printers", Hnd0 (fun () -> opt_list_printers := true),
    " list known printers";
    KLong "list-provers", Hnd0 (fun () -> opt_list_provers := true),
    " list known provers";
    KLong "list-formats", Hnd0 (fun () -> opt_list_formats := true),
    " list known input formats";
    KLong "list-metas", Hnd0 (fun () -> opt_list_metas := true),
    " list known metas";
    KLong "list-attributes", Hnd0 (fun () -> opt_list_attrs := true),
    " list used attributes";
    KLong "print-libdir", Hnd0 (fun () -> printf "%s@." Config.libdir; exit 0),
    " print location of binary components (plugins, etc)";
    KLong "print-datadir", Hnd0 (fun _ -> printf "%s@." Config.datadir; exit 0),
    " print location of non-binary data (modules, etc)";
    KLong "version",
    Hnd0 (fun _ -> printf "Why3 platform, version %s@." Config.version; exit 0),
    " print version information";
  ]

let command_path = match Config.localdir with
  | Some p -> Filename.concat p "bin"
  | None -> Filename.concat Config.libdir "commands"

let extra_help fmt commands =
  fprintf fmt "Available commands:@\n";
  List.iter (fprintf fmt "  %s@\n") commands

let tools_ext =
  if Dynlink.is_native then ".cmxs" else ".cma"

let available_commands () =
  let commands = Sys.readdir command_path in
  Array.sort String.compare commands;
  let re = Re.Str.regexp "^why3\\([^.]+\\)\\([.].*\\)" in
  let commands = Array.fold_left (fun acc v ->
    if Re.Str.string_match re v 0 then
      let w = Re.Str.matched_group 1 v in
      if Re.Str.matched_group 2 v = tools_ext then w :: acc else acc
    else acc) [] commands in
  List.rev commands

let do_usage () =
  Format.printf
    "@[Usage: %s [options] <command> [options]@\n\
     Execute the given subcommand.@\n\
     @\n%s@\n%a@]@?"
    (Filename.basename Sys.argv.(0))
    (Getopt.format option_list)
    extra_help (available_commands ());
  exit 0

let option_list =
  let open Getopt in
  (Key ('h', "help"), Hnd0 do_usage,
   " display this help and exit") ::
  option_list

let command cur =
  let sscmd, args =
    let nargs = Array.length Sys.argv in
    let sscmd = Sys.argv.(cur) in
    let cur = cur + 1 in
    if sscmd = "help" then begin
      if cur = nargs then do_usage ();
      let sscmd = Sys.argv.(cur) in
      sscmd, ["--help"]
    end else begin
      let args = ref [] in
      for i = 1 to nargs - 1 do
        if i <> cur - 1 then args := Sys.argv.(i) :: !args;
      done;
      sscmd, List.rev !args
    end in
  let cmd =
    let scmd = "why3" ^ sscmd ^ tools_ext in
    let cmd = Filename.concat command_path scmd in
    if not (Sys.file_exists cmd) then
      begin
        eprintf "'%s' is not a Why3 command.@\n@\n%a"
          sscmd extra_help (available_commands ());
        exit 1;
      end;
      cmd in
  let args = Array.of_list args in
  let argc = Array.length args in
  let argi = Array.length Sys.argv - argc in
  Array.blit args 0 Sys.argv argi argc;
  Whyconf.Args.first_arg := argi;
  try
    Dynlink.allow_unsafe_modules true;
    Dynlink.loadfile cmd;
    exit 0
  with Dynlink.Error e ->
    Printf.eprintf "Failed to load %s: %s\n%!" cmd (Dynlink.error_message e);
    exit 1

let () = try
  let i = Getopt.parse_many option_list Sys.argv 1 in
  if i < Array.length Sys.argv then command i;
  let config,_,_ = Args.complete_initialization () in

  (* listings *)

  let sort_pair (x,_) (y,_) = String.compare x y in
  let opt_list = ref false in
  if !opt_list_transforms then begin
    opt_list := true;
    let print_trans_desc fmt (x,r) =
      fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r in
    printf "@[<hov 2>Known non-splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms ()));
    printf "@[<hov 2>Known splitting transformations:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair (Trans.list_transforms_l ()));
    let list_transform_with_arg =
      Trans.list_transforms_with_args () @
      Trans.list_transforms_with_args_l () in
    printf "@[<hov 2>Known transformations with arguments:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_trans_desc)
      (List.sort sort_pair list_transform_with_arg)
  end;
  if !opt_list_printers then begin
    opt_list := true;
    let print_printer_desc fmt (s,f) =
      fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" s Pp.formatted f in
    printf "@[<hov 2>Known printers:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print_printer_desc)
      (List.sort sort_pair (Printer.list_printers ()))
  end;
  if !opt_list_formats then begin
    opt_list := true;
    let print1 fmt s = fprintf fmt "%S" s in
    let print fmt (p, l, f) =
      fprintf fmt "@[%s [%a]@\n  @[%a@]@]"
        p (Pp.print_list Pp.comma print1) l
        Pp.formatted f
    in
    printf "@[Known input formats:@\n  @[%a@]@]@."
      (Pp.print_list Pp.newline2 print)
      (List.sort (fun (u,_,_) (v,_,_) -> String.compare u v)
         (Env.list_formats Env.base_language))
  end;
  if !opt_list_provers then begin
    opt_list := true;
    let print = Pp.print_iter2 Mprover.iter Pp.newline Pp.nothing
      print_prover Pp.nothing in
    let provers = get_provers config in
    printf "@[<hov 2>Known provers:@\n%a@]@." print provers
  end;
  if !opt_list_metas then begin
    opt_list := true;
    let print fmt m = fprintf fmt "@[<h 2>%s %s%a@\n@[<hov>%a@]@]"
      (let s = m.meta_name in
        if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
      (if m.meta_excl then "(flag) " else "")
      (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
      Pp.formatted m.meta_desc
    in
    let cmp m1 m2 = String.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print) (List.sort cmp (Theory.list_metas ()))
  end;
  if !opt_list_attrs then begin
    opt_list := true;
    let l = List.sort String.compare (Ident.list_attributes ()) in
    List.iter (fun x -> Format.eprintf "%s@." x) l
  end;
  if !opt_list then exit 0;

  do_usage ();

  with
  | e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
