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
open Whyconf
open Theory

let usage_msg = sprintf
  "Usage: %s [options] <command> [options]"
  (Filename.basename Sys.argv.(0))

let version_msg = sprintf "Why3 platform, version %s (build date: %s)"
  Config.version Config.builddate

let opt_config = ref None
let opt_extra = ref []
let opt_loadpath = ref []

let opt_print_libdir = ref false
let opt_print_datadir = ref false

let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false

let opt_version = ref false
let opt_help = ref false

let option_list = Arg.align [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> Read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
  "--list-transforms", Arg.Set opt_list_transforms,
      " List known transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " List known printers";
  "--list-provers", Arg.Set opt_list_provers,
      " List known provers";
  "--list-formats", Arg.Set opt_list_formats,
      " List known input formats";
  "--list-metas", Arg.Set opt_list_metas,
      " List known metas";
  Debug.Args.desc_debug_list;
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug;
  "--print-libdir", Arg.Set opt_print_libdir,
      " Print location of binary components (plugins, etc)";
  "--print-datadir", Arg.Set opt_print_datadir,
      " Print location of non-binary data (theories, modules, etc)";
  "--version", Arg.Set opt_version,
      " Print version information";
  "--help", Arg.Set opt_help, " Display this list of options";
  "-help", Arg.Set opt_help, " Display this list of options" ]

let command_path =
  match Config.localdir with
  | Some p -> Filename.concat p "bin"
  | None -> Filename.concat Config.libdir "commands"

let available_commands () =
  let commands = Sys.readdir command_path in
  Array.sort String.compare commands;
  let re = Str.regexp "^why3\\([^.]*\\)\\([.].*\\)?" in
  let commands = Array.fold_left (fun acc v ->
    if Str.string_match re v 0 then
      let w = Str.matched_group 1 v in
      match acc with
      | (h,_)::_ when h = w -> acc
      | _ -> (w, v) :: acc
    else acc) [] commands in
  List.rev commands

let command sscmd =
  let (scmd,cmd) =
    let scmd = "why3" ^ sscmd in
    let cmd = Filename.concat command_path scmd in
    if Sys.file_exists cmd then (scmd, cmd)
    else begin
      let commands = available_commands () in
      let scmd =
	try List.assoc sscmd commands
	with Not_found ->
	  eprintf "'%s' is not a why3 command.@\n@\nAvailable commands:@." cmd;
	  List.iter (fun (v,_) -> eprintf "  %s@." v) commands;
	  exit 1 in
      let cmd = Filename.concat command_path scmd in
      (scmd, cmd)
    end in
  let args = ref [] in
  (match !opt_config with Some v -> args := v :: "-C" :: !args | None -> ());
  List.iter (fun v -> args := v :: "-L" :: !args) (List.rev !opt_loadpath);
  for i = !Arg.current + 1 to Array.length Sys.argv - 1 do
    args := Sys.argv.(i) :: !args;
  done;
  Unix.execv cmd (Array.of_list (scmd :: List.rev !args))

let () = try
  Arg.parse option_list command usage_msg;

  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end;
  if !opt_help then begin
    printf "%s@\nAvailable commands:@." (Arg.usage_string option_list usage_msg);
    List.iter (fun (v,_) -> printf "  %s@." v) (available_commands ());
    exit 0
  end;
  if !opt_print_libdir then begin
    printf "%s@." Config.libdir;
    exit 0
  end;
  if !opt_print_datadir then begin
    printf "%s@." Config.datadir;
    exit 0
  end;

  (** Configuration *)
  let config = read_config !opt_config in
  let config = List.fold_left merge_config config !opt_extra in
  let main = get_main config in
  Whyconf.load_plugins main;

  Debug.Args.set_flags_selected ();

  (** listings*)

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
      (List.sort sort_pair (Trans.list_transforms_l ()))
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
      (List.sort Pervasives.compare (Env.list_formats ()))
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
    let cmp m1 m2 = Pervasives.compare m1.meta_name m2.meta_name in
    printf "@[<hov 2>Known metas:@\n%a@]@\n@."
      (Pp.print_list Pp.newline2 print) (List.sort cmp (Theory.list_metas ()))
  end;
  opt_list :=  Debug.Args.option_list () || !opt_list;
  if !opt_list then exit 0;

  printf "%s@\n@\nAvailable commands:@." usage_msg;
  List.iter (fun (v,_) -> printf "  %s@." v) (available_commands ())

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
