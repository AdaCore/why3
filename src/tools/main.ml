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
open Whyconf
open Theory

let usage_msg = sprintf
  "Usage: %s [options] <command> [options]"
  (Filename.basename Sys.argv.(0))

let opt_list_transforms = ref false
let opt_list_printers = ref false
let opt_list_provers = ref false
let opt_list_formats = ref false
let opt_list_metas = ref false
let opt_list_labels = ref false

let option_list = [
  "--list-transforms", Arg.Set opt_list_transforms,
      " list known transformations";
  "--list-printers", Arg.Set opt_list_printers,
      " list known printers";
  "--list-provers", Arg.Set opt_list_provers,
      " list known provers";
  "--list-formats", Arg.Set opt_list_formats,
      " list known input formats";
  "--list-metas", Arg.Set opt_list_metas,
      " list known metas";
  "--list-labels", Arg.Set opt_list_labels, "list used labels";
  "--print-libdir",
      Arg.Unit (fun _ -> printf "%s@." Config.libdir; exit 0),
      " print location of binary components (plugins, etc)";
  "--print-datadir",
      Arg.Unit (fun _ -> printf "%s@." Config.datadir; exit 0),
      " print location of non-binary data (theories, modules, etc)";
  "--version",
      Arg.Unit (fun _ -> printf "Why3 platform, version %s@."
        Config.version; exit 0),
      " print version information";
]

let command_path = match Config.localdir with
  | Some p -> Filename.concat p "bin"
  | None -> Filename.concat Config.libdir "commands"

let extra_help fmt commands =
  fprintf fmt "@\nAvailable commands:@.";
  List.iter (fun (v,_) -> fprintf fmt "  %s@." v) commands

let available_commands () =
  let commands = Sys.readdir command_path in
  Array.sort String.compare commands;
  let re = Str.regexp "^why3\\([^.]+\\)\\([.].*\\)?" in
  let commands = Array.fold_left (fun acc v ->
    if Str.string_match re v 0 then
      let w = Str.matched_group 1 v in
      match acc with
      | _ when w = "contraption" -> acc
      | (h,_)::_ when h = w -> acc
      | _ -> (w, v) :: acc
    else acc) [] commands in
  List.rev commands

let command sscmd =
  let cmd =
    let scmd = "why3" ^ sscmd in
    let cmd = Filename.concat command_path scmd in
    if cmd <> "" && cmd <> "contraption" && Sys.file_exists cmd
    then cmd
    else begin
      let commands = available_commands () in
      let scmd =
        try List.assoc sscmd commands
        with Not_found ->
          eprintf "'%s' is not a Why3 command.@\n%a"
            sscmd extra_help commands;
          exit 1 in
      Filename.concat command_path scmd
    end in
  let args = ref [] in
  for i = 1 to Array.length Sys.argv - 1 do
    if i <> !Arg.current then args := Sys.argv.(i) :: !args;
  done;
  let scmd = "why3 " ^ sscmd in
  Unix.execv cmd (Array.of_list (scmd :: List.rev !args))

let () = try
  let extra_help fmt () = extra_help fmt (available_commands ()) in
  let config,_,_ = Args.initialize ~extra_help option_list command usage_msg in

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
      (List.sort Pervasives.compare (Env.list_formats Env.base_language))
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
  if !opt_list_labels then begin
    opt_list := true;
    let l = List.sort String.compare (Ident.list_label ()) in
    List.iter (fun x -> Format.eprintf "%s@." x) l
  end;
  if !opt_list then exit 0;

  printf "@[%s%a@]" usage_msg extra_help ()

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
